mod parsed_blocks;
mod source_index;
pub use source_index::ProofSourceIndex;

use std::ops::Range;
use std::sync::Arc;

use super::validation::tactic_name;
use super::*;
use crate::languages::c::target::CTarget;
use crate::languages::c::thread_runtime::CThreadRuntime;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ContractProofClaim {
    Ensure(usize),
    ExceptionalEnsure(usize),
    Grouped,
}

impl ContractProofClaim {
    /// The claim as a diagnostic names it: the zero-based source clause, or
    /// the function's one grouped proof.
    pub fn describe(&self) -> String {
        match self {
            Self::Ensure(index) => format!("`ensures` clause {index}"),
            Self::ExceptionalEnsure(index) => format!("`exceptional ensures` clause {index}"),
            Self::Grouped => "grouped contract proof".to_string(),
        }
    }
}

pub fn verifying_source_paths(click_source: &str) -> Result<Vec<String>, ClickError> {
    let tokens = plain_source_tokens(click_source)?;
    let mut paths = Vec::new();
    for window in tokens.windows(2) {
        if window[0].text == "verifying"
            && window[1].text.starts_with('"')
            && window[1].text.ends_with('"')
        {
            paths.push(window[1].text[1..window[1].text.len() - 1].to_string());
        }
    }
    Ok(paths)
}

/// Finds the top-level `target "..."` and `mode "..."` directives
/// that select the C implementation target, before any C source is
/// preprocessed. Include expansion needs the target, and expansion happens
/// before the sidecar is parsed, so this scan and the parser resolve names
/// through the same [`CTarget::from_parts`]. Absent directives select the
/// default target.
pub fn selected_c_target(click_source: &str) -> Result<CTarget, ClickError> {
    Ok(declared_c_target(click_source)?.unwrap_or(CTarget::SUPPORTED))
}

/// Scans the explicit runtime selector before the full sidecar is parsed.
/// Incremental sessions use it to refuse a changed runtime identity.
pub fn selected_thread_runtime(click_source: &str) -> Result<CThreadRuntime, ClickError> {
    let tokens = plain_source_tokens(click_source)?;
    let mut selected = None;
    let mut depth = 0usize;
    for window in tokens.windows(3) {
        match window[0].text.as_str() {
            "{" => depth += 1,
            "}" => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth > 0
            || window[0].text != "runtime"
            || !window[1].text.starts_with('"')
            || !window[1].text.ends_with('"')
            || window[1].text.len() < 2
            || window[2].text != ";"
        {
            continue;
        }
        let name = &window[1].text[1..window[1].text.len() - 1];
        let runtime = CThreadRuntime::from_name(name)
            .ok_or_else(|| ClickError::new(format!("unknown C runtime `{name}`")))?;
        if selected.replace(runtime).is_some() {
            return Err(ClickError::new(
                "a Click file declares more than one `runtime`",
            ));
        }
    }
    Ok(selected.unwrap_or_default())
}

pub fn selected_project_thread_runtime(
    project: &ClickProject,
) -> Result<CThreadRuntime, ClickError> {
    let mut selected = CThreadRuntime::None;
    for module in project.modules() {
        let runtime = selected_thread_runtime(module.source())?;
        if runtime != CThreadRuntime::None {
            if selected != CThreadRuntime::None && selected != runtime {
                return Err(ClickError::new(
                    "project modules select different C runtimes",
                ));
            }
            selected = runtime;
        }
    }
    if let Some(configured) = project.c_profile().and_then(|profile| profile.runtime) {
        if selected != CThreadRuntime::None && selected != configured {
            return Err(ClickError::new(
                "Click project config conflicts with a module `runtime` directive",
            ));
        }
        return Ok(configured);
    }
    Ok(selected)
}

/// The C implementation target one project selects. Modules may restate the
/// same target, but a project has exactly one preprocessing and proof-artifact
/// target, so two different declarations are an error.
pub fn selected_project_c_target(project: &ClickProject) -> Result<CTarget, ClickError> {
    let mut modules = project.modules().iter().collect::<Vec<_>>();
    modules.sort_by_key(|module| module.identity());
    let mut selected: Option<(&str, CTarget)> = None;
    for module in modules {
        let Some(declared) = declared_c_target(module.source())? else {
            continue;
        };
        match selected {
            Some((previous_identity, previous)) if previous != declared => {
                return Err(ClickError::new(format!(
                    "module `{}` selects C target `{}`, but module `{previous_identity}` selects `{}`",
                    module.identity(),
                    declared.name(),
                    previous.name()
                )));
            }
            _ => selected = Some((module.identity(), declared)),
        }
    }
    if let Some(configured) = project.c_profile().and_then(|profile| profile.target) {
        if let Some((identity, declared)) = selected
            && declared != configured
        {
            return Err(ClickError::new(format!(
                "Click project config selects C target `{}`, but module `{identity}` selects `{}`",
                configured.name(),
                declared.name()
            )));
        }
        return Ok(configured);
    }
    Ok(selected.map_or(CTarget::SUPPORTED, |(_, target)| target))
}

fn declared_c_target(click_source: &str) -> Result<Option<CTarget>, ClickError> {
    let tokens = plain_source_tokens(click_source)?;
    let mut target = None;
    let mut mode = None;
    let mut depth = 0usize;
    for window in tokens.windows(3) {
        // The directives are file items, so only brace depth zero can hold
        // one. A deeper `target "..."` spelling is not a directive here and
        // must not be one for the parser either.
        match window[0].text.as_str() {
            "{" => depth += 1,
            "}" => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth > 0
            || !window[1].text.starts_with('"')
            || !window[1].text.ends_with('"')
            || window[1].text.len() < 2
            || window[2].text != ";"
        {
            continue;
        }
        let slot = match window[0].text.as_str() {
            "target" => &mut target,
            "mode" => &mut mode,
            _ => continue,
        };
        if slot.is_some() {
            return Err(ClickError::new(format!(
                "a Click file declares more than one `{}`",
                window[0].text
            )));
        }
        *slot = Some(&window[1].text[1..window[1].text.len() - 1]);
    }
    if target.is_none() && mode.is_none() {
        return Ok(None);
    }
    CTarget::from_parts(target, mode)
        .map(Some)
        .map_err(|message| ClickError::new(message).with_kind(ClickErrorKind::Type))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickImportSite {
    pub path: String,
    pub position: SourcePosition,
}

/// Finds top-level import declarations for the filesystem graph loader. Full
/// syntax and interface validation still happens in the shared parser.
pub fn click_import_sites(click_source: &str) -> Result<Vec<ClickImportSite>, ClickError> {
    click_import_sites_in_container(click_source, None)
}

pub(crate) fn click_import_sites_in_container(
    click_source: &str,
    container: Option<&crate::source::SourceContainer>,
) -> Result<Vec<ClickImportSite>, ClickError> {
    let tokens = parser::source_tokens_in_container(click_source, container)?;
    let mut sites = Vec::new();
    for window in tokens.windows(2) {
        if window[0].text == "import"
            && window[1].text.starts_with('"')
            && window[1].text.ends_with('"')
        {
            sites.push(ClickImportSite {
                path: window[1].text[1..window[1].text.len() - 1].to_string(),
                position: position_at_offset(click_source, window[0].span.start),
            });
        }
    }
    Ok(sites)
}

/// Expands one claim and returns the rewritten source.
///
/// The caller is responsible for verifying the returned sidecar.
pub fn expand_c_claim_source(
    click_source: &str,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: ContractProofClaim,
) -> Result<String, ClickError> {
    let sources = ProgramSourceContext::bundle(c_sources);
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    let tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let function_block = proof_function_blocks(&file)
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let function = DeclarationSources::new(&tokens).function(function_block)?;
    let claim = covering_claim(function_block, claim);
    let edit = if claim == ContractProofClaim::Grouped {
        find_grouped_proof_edit(&tokens, &function, function_block)?
    } else {
        find_claim_proof_edit(&tokens, &function, function_block, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = verify_c_sources_at(click_source, c_sources, target.line, target.column)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = claim_expansion_source(click_source, theorem)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => {
            unreachable!("function claim edits are never loop phases")
        }
    };
    let expanded = splice_source(click_source, &tokens, span, &replacement)?;
    checked_expanded_source(click_source, &sources, &replacement, expanded).map_err(|error| {
        error.with_context(format!(
            "expanding `{function_name}` {} at {target}",
            claim.describe()
        ))
    })
}

// The proof checker can use its compatibility rules without a Surface replay.
// The formatter keeps that provenance even in nested or flattened proof edits.
pub(super) fn require_surface_expansion(rendered: String) -> Result<String, ClickError> {
    if rendered.contains(printing::COMPATIBILITY_NORMALIZATION) {
        return Err(ClickError::new(
            "proof expansion is unavailable: verification used legacy normalization and no ordinary proof was recorded",
        ).with_kind(ClickErrorKind::Unsupported));
    }
    Ok(rendered)
}

/// Formats a function claim's already-checked certificate into its source.
/// Returns `None` for claims not represented in `verified` or not declared in
/// this source module. The caller must verify the rewritten source, and must
/// run this on the thread retaining the verification's kernel tables.
pub fn expand_verified_function_claim_source_by_label(
    click_source: &str,
    verified: &[VerifiedProgramTheorem],
    claim_label: &str,
) -> Result<Option<String>, ClickError> {
    let Some((function_block, claim)) = verified.iter().find_map(|theorem| {
        function_expansion_claim_by_label(&theorem.function_block, claim_label)
            .map(|claim| (&theorem.function_block, claim))
    }) else {
        return Ok(None);
    };
    let function_name = function_block.signature().name();
    let tokens = proof_source_tokens(click_source, &function_block.parsed_body().implicit_proofs)?;
    let Ok(function) = DeclarationSources::new(&tokens).function(function_block) else {
        return Ok(None);
    };
    let claim = covering_claim(function_block, claim);
    let edit = if claim == ContractProofClaim::Grouped {
        find_grouped_proof_edit(&tokens, &function, function_block)?
    } else {
        find_claim_proof_edit(&tokens, &function, function_block, claim)?
    };
    let theorem = select_expansion_theorem(verified, function_name, claim)?;
    let replacement = claim_expansion_source(click_source, theorem)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => unreachable!(),
    };
    Ok(Some(splice_source(
        click_source,
        &tokens,
        span,
        &replacement,
    )?))
}

fn expand_project_claim_source(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    function_name: &str,
    claim: ContractProofClaim,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    let tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let function_block = proof_function_blocks(&file)
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let function = DeclarationSources::new(&tokens).function(function_block)?;
    let claim = covering_claim(function_block, claim);
    let edit = if claim == ContractProofClaim::Grouped {
        find_grouped_proof_edit(&tokens, &function, function_block)?
    } else {
        find_claim_proof_edit(&tokens, &function, function_block, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = verify_project_at(project, inputs, target.line, target.column)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = claim_expansion_source(click_source, theorem)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => unreachable!(),
    };
    let expanded = splice_source(click_source, &tokens, span, &replacement)?;
    let rewritten = project.with_entry_source(expanded.clone());
    let rewritten_sources = ProgramSourceContext::of(inputs)?.with_click_project(&rewritten);
    resolve_click_project_context(&rewritten, &rewritten_sources)
        .map(|_| expanded)
        .map_err(|error| {
            unparseable_expansion_error_for_file(&replacement, error, Some(&file)).with_context(
                format!(
                    "expanding `{function_name}` {} at {target}",
                    claim.describe()
                ),
            )
        })
}

fn expand_c_prepared_claim_source(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    function_name: &str,
    claim: ContractProofClaim,
) -> Result<String, ClickError> {
    let sources = ProgramSourceContext::prepared(imports);
    let file = parse_source_with_program_layouts_context(click_source, &sources)?;
    let tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let function_block = proof_function_blocks(&file)
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let function = DeclarationSources::new(&tokens).function(function_block)?;
    let claim = covering_claim(function_block, claim);
    let edit = if claim == ContractProofClaim::Grouped {
        find_grouped_proof_edit(&tokens, &function, function_block)?
    } else {
        find_claim_proof_edit(&tokens, &function, function_block, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = verify_sources_at(
        click_source,
        &ProgramInputs::Prepared(imports),
        target.line,
        target.column,
    )?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = claim_expansion_source(click_source, theorem)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => unreachable!(),
    };
    let expanded = splice_source(click_source, &tokens, span, &replacement)?;
    checked_expanded_source(click_source, &sources, &replacement, expanded).map_err(|error| {
        error.with_context(format!(
            "expanding `{function_name}` {} at {target}",
            claim.describe()
        ))
    })
}

/// Use the same claim labels for every source/import route. A selected
/// exceptional ensure must remain exceptional through lookup; covering_claim
/// subsequently selects the grouped proof when that is its producer.
fn function_expansion_claim_by_label(
    function: &FunctionBlock,
    claim_label: &str,
) -> Option<ContractProofClaim> {
    function.claim_by_label(claim_label).or_else(|| {
        (has_body_safety_proof(function)
            && [
                claim_labels::body_safety_label(function.signature().name()),
                function.ensure_claim_label(0),
                function.contract_claim_label(),
            ]
            .iter()
            .any(|label| label == claim_label))
        .then_some(ContractProofClaim::Grouped)
    })
}

/// A function with no stated outcomes still has a proof of body safety.
/// Expansion writes that proof after the contract, without inventing a source
/// postcondition or changing the verifier's per-claim proof protocol.
fn has_body_safety_proof(function: &FunctionBlock) -> bool {
    !function.is_external()
        && !function.is_tactic_procedure()
        && function.ensures().is_empty()
        && function.exceptional_ensures().is_empty()
}

fn expansion_covering_proof(function: &FunctionBlock) -> Option<&SourceProof> {
    static BODY_SAFETY: SourceProof = SourceProof::Tactic(SmartTactic::ImplicitTail);
    function
        .covering_proof()
        .or_else(|| has_body_safety_proof(function).then_some(&BODY_SAFETY))
}

/// Expands one function claim selected by the same stable label used by
/// profiling and diagnostics.
pub fn expand_c_claim_source_by_label(
    click_source: &str,
    c_sources: &[(&str, &str)],
    claim_label: &str,
) -> Result<String, ClickError> {
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    for theorem in file.theorem_definitions() {
        if let Some(index) = theorem.ensure_index_by_label(claim_label) {
            return expand_pure_theorem_source(click_source, c_sources, theorem.name(), index);
        }
    }
    for function in proof_function_blocks(&file) {
        if let Some(claim) = function_expansion_claim_by_label(function, claim_label) {
            return expand_c_claim_source(
                click_source,
                c_sources,
                function.signature().name(),
                claim,
            );
        }
    }
    if let Some(expansion) = expand_loop_phase_claim(
        None,
        click_source,
        &ProgramInputs::Bundle(c_sources.to_vec()),
        &ProgramSourceContext::bundle(c_sources),
        &file,
        claim_label,
        None,
    )? {
        return Ok(expansion.source);
    }
    Err(ClickError::new(format!(
        "could not locate function claim `{claim_label}`"
    )))
}

pub fn expand_project_claim_source_by_label(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    claim_label: &str,
) -> Result<String, ClickError> {
    project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    let compiler_imported = matches!(inputs, ProgramInputs::Program(_));
    let claim_label = &*resolve_source_claim_label(&file, claim_label);
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        if let Some(index) = theorem.ensure_index_by_label(claim_label) {
            return expand_project_pure_theorem_source(project, inputs, theorem.name(), index);
        }
    }
    for function in proof_function_blocks(&file) {
        if let Some(claim) = function_expansion_claim_by_label(function, claim_label) {
            return expand_project_claim_source(
                project,
                inputs,
                function.signature().name(),
                claim,
            );
        }
    }
    let click_source = project.entry_source().expect("resolved entry source");
    if let Some(expansion) = expand_loop_phase_claim(
        Some(project),
        click_source,
        inputs,
        &sources,
        &file,
        claim_label,
        None,
    )? {
        return Ok(expansion.source);
    }
    Err(ClickError::new(format!(
        "could not locate {}function claim `{claim_label}`",
        if compiler_imported {
            "compiler-imported "
        } else {
            ""
        }
    )))
}

pub fn expand_c_prepared_claim_source_by_label(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    claim_label: &str,
) -> Result<String, ClickError> {
    let sources = ProgramSourceContext::prepared(imports);
    let file = parse_source_with_program_layouts_context(click_source, &sources)?;
    for theorem in file.theorem_definitions() {
        if let Some(index) = theorem.ensure_index_by_label(claim_label) {
            return expand_pure_theorem_source_context(
                click_source,
                &sources,
                theorem.name(),
                index,
            );
        }
    }
    for function in proof_function_blocks(&file) {
        if let Some(claim) = function_expansion_claim_by_label(function, claim_label) {
            return expand_c_prepared_claim_source(
                click_source,
                imports,
                function.signature().name(),
                claim,
            );
        }
    }
    if let Some(expansion) = expand_loop_phase_claim(
        None,
        click_source,
        &ProgramInputs::Prepared(imports),
        &sources,
        &file,
        claim_label,
        None,
    )? {
        return Ok(expansion.source);
    }
    Err(ClickError::new(format!(
        "could not locate function claim `{claim_label}`"
    )))
}

pub fn expand_program_prepared_claim_source_by_label(
    click_source: &str,
    import: impl Into<crate::languages::PreparedProgram>,
    claim_label: &str,
) -> Result<String, ClickError> {
    expand_program_prepared_claim_source_by_label_context(click_source, import, claim_label)
}

fn expand_program_prepared_claim_source_by_label_context(
    click_source: &str,
    import: impl Into<crate::languages::PreparedProgram>,
    claim_label: &str,
) -> Result<String, ClickError> {
    let import = import.into();
    let sources = ProgramSourceContext::program(&import)?;
    let file = parse_source_with_program_layouts_context(click_source, &sources)?;
    let claim_label = &*resolve_source_claim_label(&file, claim_label);
    for theorem in file.theorem_definitions() {
        if let Some(index) = theorem.ensure_index_by_label(claim_label) {
            let verified = verify_click_theorem_context(click_source, &sources, theorem.name())?;
            return rewrite_verified_pure_theorem(click_source, &verified, theorem.name(), index);
        }
    }
    for function in proof_function_blocks(&file) {
        if let Some(claim) = function_expansion_claim_by_label(function, claim_label) {
            return expand_program_prepared_claim_source_context(
                click_source,
                &import,
                function.signature().name(),
                claim,
            );
        }
    }
    if let Some(expansion) = expand_loop_phase_claim(
        None,
        click_source,
        &ProgramInputs::Program(import),
        &sources,
        &file,
        claim_label,
        None,
    )? {
        return Ok(expansion.source);
    }
    Err(ClickError::new(format!(
        "could not locate compiler-imported function claim `{claim_label}`"
    )))
}

fn expand_program_prepared_claim_source_context(
    click_source: &str,
    import: &crate::languages::PreparedProgram,
    function_name: &str,
    claim: ContractProofClaim,
) -> Result<String, ClickError> {
    let sources = ProgramSourceContext::program(import)?;
    let file = parse_source_with_program_layouts_context(click_source, &sources)?;
    let tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let function_block = proof_function_blocks(&file)
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let function = DeclarationSources::new(&tokens).function(function_block)?;
    let claim = covering_claim(function_block, claim);
    let edit = if claim == ContractProofClaim::Grouped {
        find_grouped_proof_edit(&tokens, &function, function_block)?
    } else {
        find_claim_proof_edit(&tokens, &function, function_block, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = verify_sources_at(
        click_source,
        &ProgramInputs::program(import),
        target.line,
        target.column,
    )?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = claim_expansion_source(click_source, theorem)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => unreachable!(),
    };
    let expanded = splice_source(click_source, &tokens, span, &replacement)?;
    checked_expanded_source(click_source, &sources, &replacement, expanded).map_err(|error| {
        error.with_context(format!(
            "expanding `{function_name}` {} at {target}",
            claim.describe()
        ))
    })
}

/// What `click expand --claim` rewrote: the source, and the label of the
/// proof unit whose verification checks the rewrite. That is the claim
/// itself, except for a loop phase proved inside a claim's proof script,
/// which that claim's proof checks.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClaimExpansion {
    pub source: String,
    pub proof_unit: String,
}

/// Expands one claim selected by its label, from any input kind: a function
/// or theorem claim, or a loop phase `f.loop(N).initialize` or
/// `f.loop(N).maintain`. With `project`, `click_source` is ignored and the
/// project's entry module is rewritten.
///
/// `at`, a location of the claim's source such as [`claim_at`] reports,
/// chooses among several `loop` tactics that prove the one loop phase the
/// label names.
///
/// The caller is responsible for verifying the returned sidecar, by
/// `proof_unit`.
pub fn expand_claim_by_label(
    project: Option<&ClickProject>,
    click_source: &str,
    inputs: &ProgramInputs<'_>,
    claim_label: &str,
    at: Option<SourcePosition>,
) -> Result<ClaimExpansion, ClickError> {
    let click_source = match project {
        Some(project) => project.entry_source().ok_or_else(|| {
            ClickError::new(format!("missing entry module `{}`", project.entry()))
        })?,
        None => click_source,
    };
    let sources = match project {
        Some(project) => ProgramSourceContext::of(inputs)?.with_click_project(project),
        None => ProgramSourceContext::of(inputs)?,
    };
    let file = match project {
        Some(project) => resolve_click_project_context(project, &sources)?,
        None => parse_source_with_program_layouts_context(click_source, &sources)?,
    };
    if claim_label == "program.termination" {
        let _binder_names =
            printing::CertificateBinderScope::enter(click_source, file.function_blocks());
        let (result, certificate) = capture_termination_certificate(|| {
            crate::surface::verification::verify_program_with_context(
                click_source,
                &sources,
                None,
                None,
                None,
                Some(file.clone()),
            )
        });
        result?;
        let certificate =
            certificate.expect("successful program verification publishes its proof certificate");
        let replacement = require_surface_expansion(format!(
            "termination {}\n",
            printing::format_proof_certificate(&certificate)
        ))?;
        let source = if let Some((start, end)) = &file.termination_span {
            let first = offset_at_position(click_source, start.line, start.column)?;
            let last = offset_at_position(click_source, end.line, end.column)? + 1;
            format!(
                "{}{}{}",
                &click_source[..first],
                replacement,
                &click_source[last..]
            )
        } else {
            format!("{click_source}\n{replacement}")
        };
        return Ok(ClaimExpansion {
            source,
            proof_unit: claim_label.to_string(),
        });
    }
    let at = at
        .map(|at| offset_at_position(click_source, at.line, at.column))
        .transpose()?;
    if let Some(expansion) = expand_loop_phase_claim(
        project,
        click_source,
        inputs,
        &sources,
        &file,
        claim_label,
        at,
    )? {
        return Ok(expansion);
    }
    let source = match (project, inputs) {
        (Some(project), inputs) => {
            expand_project_claim_source_by_label(project, inputs, claim_label)
        }
        (None, ProgramInputs::Bundle(c_sources)) => {
            expand_c_claim_source_by_label(click_source, c_sources, claim_label)
        }
        (None, ProgramInputs::Prepared(imports)) => {
            expand_c_prepared_claim_source_by_label(click_source, imports, claim_label)
        }
        (None, ProgramInputs::Program(import)) => {
            expand_program_prepared_claim_source_by_label_context(click_source, import, claim_label)
        }
    }?;
    Ok(ClaimExpansion {
        source,
        proof_unit: claim_label.to_string(),
    })
}

/// Expands the loop phase `claim_label` names, if it names one: its written
/// proof is replaced by the phase's checked certificate, and an omitted
/// phase gets an explicit `initialize by { ... }` or `maintain by { ... }`.
///
/// A loop phase is proved by a `loop` tactic written in a claim's proof
/// script, and is part of that claim's proof: the source does not name the
/// C loop the tactic proves, checked execution binds it. The tactic's own
/// checked expansion, the bound loop with both phases' certificates,
/// supplies the phase, and the claim is the proof unit that checks the
/// rewrite.
fn expand_loop_phase_claim(
    project: Option<&ClickProject>,
    click_source: &str,
    inputs: &ProgramInputs<'_>,
    sources: &ProgramSourceContext<'_>,
    file: &ClickFile,
    claim_label: &str,
    at: Option<usize>,
) -> Result<Option<ClaimExpansion>, ClickError> {
    let claim_label = &*resolve_source_claim_label(file, claim_label);
    let Some((function_block, loop_index, phase)) = proof_function_blocks(file).find_map(|block| {
        let (loop_index, phase) =
            claim_labels::parse_loop_phase_claim_label(block.signature().name(), claim_label)?;
        Some((block, loop_index, loop_phase_keyword(phase)))
    }) else {
        return Ok(None);
    };
    let function_name = function_block.signature().name();
    let source_tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let tokens = ProofTokens::new(file, &source_tokens);
    let _reference_result_source = super::diagnostics::ReferenceResultSourceScope::enter(
        function_block.signature().returns_reference(),
    );
    let _parameter_places = super::diagnostics::ParameterPlaceScope::enter(function_block);
    let written = written_loop_tactics(click_source, &tokens, file)?
        .into_iter()
        .filter(|tactic| tactic.function_name == function_name)
        .collect::<Vec<_>>();
    if written.is_empty() {
        return Err(ClickError::new(format!(
            "could not locate loop phase `{claim_label}`: the proofs of `{function_name}` write no `loop` tactic"
        )));
    }
    let bound = bind_written_loop_tactics(click_source, sources, file, &written);
    let mut matching = written
        .iter()
        .zip(bound)
        .filter_map(|(tactic, clause)| match clause {
            Ok(clause) if clause.region() == &CodeRegion::Loop(loop_index) => {
                Some(Ok((tactic, clause)))
            }
            Ok(_) => None,
            Err(error) => Some(Err(error)),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if matching.len() > 1
        && let Some(at) = at
    {
        matching.retain(|(tactic, _)| tactic.anchor <= at && at < tokens[tactic.close].span.end);
    }
    let (tactic, clause) = match matching.len() {
        1 => matching.remove(0),
        0 => {
            return Err(ClickError::new(format!(
                "could not locate loop phase `{claim_label}`: no `loop` tactic in `{function_name}`'s proofs proves loop({loop_index})"
            )));
        }
        several => {
            return Err(ClickError::new(format!(
                "loop phase `{claim_label}` is proved by {several} `loop` tactics, at Click source {}; select one by a line of its phase proof, `--claim FILE:LINE`",
                matching
                    .iter()
                    .map(|(tactic, _)| {
                        let position = position_at_offset(click_source, tactic.anchor);
                        format!("{}:{}", position.line, position.column)
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            )));
        }
    };
    let proof = match phase {
        "initialize" => clause.initialize_proof(),
        "maintain" => clause.preserve_proof(),
        "otherwise" => clause.otherwise_proof(),
        _ => unreachable!("unknown loop phase"),
    };
    let tactics = proof
        .and_then(SourceProof::tactics)
        .ok_or_else(|| {
            ClickError::new(format!(
                "the checked `loop` tactic retained no `{phase}` certificate for `{claim_label}`"
            ))
        })?
        .to_vec();
    // A phase with nothing to prove is checked by `close();`, as its
    // expansion by location writes it: a `by` block holds at least one tactic.
    let tactics = if tactics.is_empty() && phase != "otherwise" {
        vec![ProofTactic::Known]
    } else {
        tactics
    };
    let edit = written_loop_phase(&tokens, tactic, phase)?.1;
    let located = LocatedSourceTactic {
        site: tactic.located.site.clone(),
        source_index: 0,
        nested: Vec::new(),
        edit: TacticSourceEdit::WholeProof(edit),
        sibling_starts: Vec::new(),
        function_block: None,
        source_spans: file.source_spans().clone(),
    };
    let (span, replacement) = located.replacement(click_source, file, &tactics)?;
    let replacement = if phase == "otherwise" {
        replacement
            .strip_prefix("by ")
            .expect("expanded proof begins with by")
    } else {
        &replacement
    };
    let replacement = indent_replacement(click_source, span.start, replacement);
    let expanded = splice_source(click_source, &tokens, &span, &replacement)?;
    let source = match project {
        Some(project) => {
            let rewritten = project.with_entry_source(expanded.clone());
            let rewritten_sources =
                ProgramSourceContext::of(inputs)?.with_click_project(&rewritten);
            match resolve_click_project_context(&rewritten, &rewritten_sources) {
                Ok(_) => expanded,
                Err(error) => {
                    return Err(unparseable_expansion_error_for_file(
                        &replacement,
                        error,
                        Some(file),
                    ));
                }
            }
        }
        None => checked_expanded_source(click_source, sources, &replacement, expanded)?,
    };
    Ok(Some(ClaimExpansion {
        source,
        proof_unit: tactic.claim_label.clone(),
    }))
}

/// The phase keyword a loop phase label spells, as a static name.
fn loop_phase_keyword(phase: &str) -> &'static str {
    match phase {
        "initialize" => "initialize",
        "maintain" => "maintain",
        "otherwise" => "otherwise",
        _ => unreachable!("unknown loop phase"),
    }
}

/// A `loop` tactic written in a function claim's proof script. The C loop it
/// proves is the one checked execution reaches there; the source does not
/// name it.
#[derive(Clone, Debug)]
struct WrittenLoopTactic {
    /// The function whose proof writes it.
    function_name: String,
    /// The tactic as source selection addresses it in its claim's proof.
    located: LocatedSourceTactic,
    /// The label of the claim whose proof writes it.
    claim_label: String,
    /// Where the `loop` keyword starts.
    anchor: usize,
    /// The tactic's token range, as the parser read it.
    range: Range<usize>,
    /// The token index of the brace that closes its body.
    close: usize,
}

/// Every `loop` tactic written in a function's proofs, in source order.
fn written_loop_tactics(
    click_source: &str,
    tokens: &ProofTokens<'_>,
    file: &ClickFile,
) -> Result<Vec<WrittenLoopTactic>, ClickError> {
    let mut written = Vec::new();
    for entry in source_tactic_entries(click_source, file)? {
        let EntrySelection::Located(located) = entry.selection else {
            continue;
        };
        let ProofSite::FunctionClaim { function_name, .. } = &located.site else {
            continue;
        };
        if entry.tactic_name != "loop" {
            continue;
        }
        let function_name = function_name.clone();
        let first = tokens.partition_point(|token| token.span.start < entry.anchor);
        let keyword = tokens[first..]
            .iter()
            .take_while(|token| token.span.start == entry.anchor)
            .position(|token| token.text == "loop")
            .map(|offset| first + offset)
            .ok_or_else(|| ClickError::new("could not locate a source `loop` tactic"))?;
        let range = tokens
            .blocks
            .tactic(keyword)
            .ok_or_else(|| ClickError::new("the parser read no `loop` tactic here"))?;
        // The body's `}` ends the tactic, before any redundant `;`.
        let close = (keyword..range.end)
            .rev()
            .find(|&index| tokens[index].text == "}" && !tokens[index].span.is_empty())
            .ok_or_else(|| ClickError::new("source `loop` tactic has no body"))?;
        written.push(WrittenLoopTactic {
            function_name,
            located,
            claim_label: entry.claim_label,
            anchor: entry.anchor,
            range,
            close,
        });
    }
    Ok(written)
}

/// Where a written `loop` tactic's `phase` proof is: the `phase` keyword's
/// start and the edit that replaces its `by` clause, or, for a phase the
/// tactic leaves to automation, the edit that writes one before the body's
/// closing brace.
fn written_loop_phase(
    tokens: &ProofTokens<'_>,
    tactic: &WrittenLoopTactic,
    phase: &'static str,
) -> Result<(Option<usize>, ProofSourceEdit), ClickError> {
    if let Some((keyword, clause)) = tokens.loop_phase(&tactic.range, phase) {
        return Ok((
            Some(tokens[keyword].span.start),
            ProofSourceEdit::Explicit(clause.span(tokens)),
        ));
    }
    let insertion = tokens[tactic.close].span.start;
    Ok((
        None,
        ProofSourceEdit::OmittedLoopPhase {
            span: insertion..insertion,
            selector: tactic.anchor,
            phase,
        },
    ))
}

/// The checked expansion of each written `loop` tactic: the loop clause
/// bound to the C loop it proves, with both phases' certificates. Each is
/// captured as the selected tactic of its own verification, as expanding it
/// by its location does; a `loop` tactic nested in another's phase is
/// checked inside that one's capture, so the two are not captured together.
fn bind_written_loop_tactics(
    click_source: &str,
    sources: &ProgramSourceContext<'_>,
    file: &ClickFile,
    written: &[WrittenLoopTactic],
) -> Vec<Result<StructuralClause, ClickError>> {
    written
        .iter()
        .map(|tactic| {
            crate::instrumentation::record_deterministic_work(1);
            let located = &tactic.located;
            let mut capture = ExpansionCapture::for_nested_tactic(
                located.site.clone(),
                located.source_index,
                &located.nested,
            );
            take_expansion_replaces_from();
            let verification = instrumentation::with_default_tactic_limits(|| {
                crate::surface::verification::verify_program_with_context(
                    click_source,
                    sources,
                    None,
                    None,
                    Some(&mut capture),
                    Some(file.clone()),
                )
            });
            take_expansion_replaces_from();
            let result = match &capture.nested {
                Some(nested) => nested.result(),
                None => capture.result.clone(),
            };
            let position = position_at_offset(click_source, tactic.anchor);
            match result {
                Some(Ok(tactics)) => match tactics.as_slice() {
                    [ProofTactic::Loop(clause)] => Ok(clause.clone()),
                    _ => Err(ClickError::new(format!(
                        "the `loop` tactic at {}:{} did not expand to one bound loop",
                        position.line, position.column
                    ))),
                },
                Some(Err(error)) => Err(ClickError::new(error)),
                None => Err(match verification {
                    Err(error) => error.with_context(format!(
                        "the proof did not check the `loop` tactic at {}:{}",
                        position.line, position.column
                    )),
                    Ok(_) => ClickError::new(format!(
                        "checked execution never reached the `loop` tactic at {}:{}",
                        position.line, position.column
                    )),
                }),
            }
        })
        .collect()
}

pub use crate::source::SourcePosition;

/// One source-selectable smart tactic in a parsed `.click` sidecar.
///
/// This inventory is purely syntactic: producing it does not execute or verify
/// any proof. `source_index` uses the same pre-order indexing as tactic timing
/// and individual source expansion. Tactics inside a `have` share its
/// claim-level index; `position` identifies each selectable nested site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmartTacticSourceSite {
    pub claim_label: String,
    pub source_index: usize,
    pub tactic_name: String,
    /// Exact source position, including tactics nested inside a `have` body.
    pub position: SourcePosition,
}

/// A written legacy normalization tactic, addressed in the entry source.
pub struct NormalizeSourceSite {
    pub claim: String,
    pub position: SourcePosition,
    pub offset: usize,
    pub using: bool,
}

pub fn normalize_source_sites(
    project: Option<&ClickProject>,
    source: &str,
    inputs: &ProgramInputs<'_>,
) -> Result<Vec<NormalizeSourceSite>, ClickError> {
    let file = normalize_source_file(project, source, inputs)?;
    let tokens = proof_source_tokens(source, &file.source_spans().implicit_proofs)?;
    let entries = source_tactic_entries_with_tokens(&file, &ProofTokens::new(&file, &tokens))?;
    // Use the flat written tactic index for identity. The token after the
    // empty arguments distinguishes the premise-list form without rewriting it.
    let mut sites = std::collections::BTreeMap::new();
    for entry in entries
        .into_iter()
        .filter(|entry| entry.tactic_name == "normalize")
    {
        let index = tokens.partition_point(|token| token.span.start < entry.anchor);
        let mut call = tokens[index..]
            .iter()
            .filter(|token| !token.span.is_empty());
        let prefix = [call.next(), call.next(), call.next()];
        if !prefix
            .iter()
            .zip(["normalize", "(", ")"])
            .all(|(token, text)| token.is_some_and(|token| token.text == text))
        {
            return Err(ClickError::new(
                "could not locate the written normalize tactic",
            ));
        }
        let using = call.next().is_some_and(|token| token.text == "using");
        sites
            .entry(entry.anchor)
            .or_insert_with(|| NormalizeSourceSite {
                claim: entry.claim_label,
                position: position_at_offset(source, entry.anchor),
                offset: entry.anchor,
                using,
            });
    }
    Ok(sites.into_values().collect())
}

/// Find a legacy call anywhere in the proof unit's source, including
/// generated proof bodies whose tactics are not individually indexed.
pub fn first_normalize_in_claim(
    project: Option<&ClickProject>,
    source: &str,
    inputs: &ProgramInputs<'_>,
    claim: &str,
) -> Result<Option<SourcePosition>, ClickError> {
    if !source.contains("normalize") {
        return Ok(None);
    }
    let file = normalize_source_file(project, source, inputs)?;
    let mut regions = claim_source_regions(source, &file, ClaimLocationScope::ProofUnit)?;
    regions.retain(|region| region.label == claim);
    if regions.is_empty() {
        return Err(ClickError::new(format!(
            "could not locate proof unit `{claim}`"
        )));
    }
    let site = plain_source_tokens(source)?
        .windows(3)
        .find(|tokens| {
            tokens[0].text == "normalize"
                && tokens[1].text == "("
                && tokens[2].text == ")"
                && regions
                    .iter()
                    .any(|region| region.span.contains(&tokens[0].span.start))
        })
        .map(|tokens| tokens[0].start.clone());
    Ok(site)
}

fn normalize_source_file(
    project: Option<&ClickProject>,
    source: &str,
    inputs: &ProgramInputs<'_>,
) -> Result<ClickFile, ClickError> {
    let sources = ProgramSourceContext::of(inputs)?;
    match project {
        Some(project) => {
            resolve_click_project_context(project, &sources.with_click_project(project))
        }
        None => parse_source_with_program_layouts_context(source, &sources),
    }
}

pub fn c_smart_tactic_source_sites(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    smart_tactic_source_sites(click_source, &ProgramInputs::Bundle(c_sources.to_vec()))
}

pub fn smart_tactic_source_sites(
    click_source: &str,
    inputs: &ProgramInputs<'_>,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    smart_tactic_source_sites_context(click_source, &ProgramSourceContext::of(inputs)?)
}

pub fn project_smart_tactic_source_sites(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    smart_tactic_source_sites_file(
        project.entry_source().expect("resolved entry source"),
        &file,
    )
}

fn smart_tactic_source_sites_context(
    click_source: &str,
    sources: &ProgramSourceContext<'_>,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let file = parse_source_with_program_layouts_context(click_source, sources)?;
    smart_tactic_source_sites_file(click_source, &file)
}

fn smart_tactic_source_sites_file(
    click_source: &str,
    file: &ClickFile,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    smart_tactic_sites_from_entries(click_source, source_tactic_entries(click_source, file)?)
}

fn smart_tactic_sites_from_entries(
    click_source: &str,
    entries: Vec<SourceTacticEntry>,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let mut sites = Vec::new();
    let mut ordered = Vec::new();
    let mut seen = BTreeSet::new();
    for entry in entries {
        if !entry.smart {
            continue;
        }
        let EntrySelection::Located(located) = entry.selection else {
            continue;
        };
        // A written script's implicit tail is selectable by location, but
        // whether it has work is known only once the proof runs; `click
        // audit` finds the claims whose tail ran from their verification.
        if matches!(located.edit, TacticSourceEdit::Append(_)) {
            continue;
        }
        // A smart container owns its body's expansion. Its written child
        // aliases select that same site and must not be counted again.
        if seen.insert((
            entry.claim_label.clone(),
            located.source_index,
            located.nested,
        )) {
            ordered.push((entry.anchor, sites.len()));
            sites.push(SmartTacticSourceSite {
                claim_label: entry.claim_label,
                source_index: located.source_index,
                tactic_name: entry.tactic_name,
                position: SourcePosition::new(1, 1),
            });
        }
    }
    ordered.sort_unstable();
    // Walk characters once, including Unicode columns. Rescanning the whole
    // prefix at every anchor would make a one-line certificate quadratic.
    let mut next = 0;
    let mut line = 1;
    let mut column = 1;
    for (offset, character) in click_source
        .char_indices()
        .chain(std::iter::once((click_source.len(), '\0')))
    {
        while ordered
            .get(next)
            .is_some_and(|(wanted, _)| *wanted == offset)
        {
            sites[ordered[next].1].position = SourcePosition::new(line, column);
            next += 1;
        }
        if next == ordered.len() {
            break;
        }
        if character == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    if next != ordered.len() {
        return Err(ClickError::new(
            "smart tactic anchor is not a source character boundary",
        ));
    }
    Ok(sites)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum VerificationTarget {
    Function(String),
    Functions(BTreeSet<String>),
    Theorem(String),
}

pub(super) fn verification_target_at(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<VerificationTarget, ClickError> {
    let sources = ProgramSourceContext::bundle(c_sources);
    verification_target_at_context(click_source, &sources, line, column)
}

pub(super) fn verification_target_at_context(
    click_source: &str,
    c_sources: &ProgramSourceContext<'_>,
    line: usize,
    column: usize,
) -> Result<VerificationTarget, ClickError> {
    let file = parse_source_with_program_layouts_context(click_source, c_sources)?;
    verification_target_at_file(click_source, &file, line, column)
}

pub(in crate::surface) fn verification_target_at_file(
    click_source: &str,
    file: &ClickFile,
    line: usize,
    column: usize,
) -> Result<VerificationTarget, ClickError> {
    let wanted = offset_at_position(click_source, line, column)?;
    if let Some((start, end)) = &file.termination_span {
        let first = offset_at_position(click_source, start.line, start.column)?;
        let last = offset_at_position(click_source, end.line, end.column)?;
        if first <= wanted && wanted <= last {
            return Ok(VerificationTarget::Functions(
                file.function_blocks()
                    .iter()
                    .filter(|block| file.function_is_selected(block.signature().name()))
                    .map(|block| block.signature().name().to_string())
                    .chain(
                        file.tactic_definitions()
                            .iter()
                            .map(|tactic| tactic.name().to_string()),
                    )
                    .collect(),
            ));
        }
    }
    let tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let declarations = DeclarationSources::new(&tokens);
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        let source = declarations.theorem(theorem)?;
        if tokens[source.body_open].span.start <= wanted
            && wanted <= tokens[source.body_close].span.end
        {
            return Ok(VerificationTarget::Theorem(theorem.name().to_string()));
        }
    }
    for function in proof_function_blocks(file) {
        let function_name = function.signature().name();
        let source = declarations.function(function)?;
        let in_body = tokens[source.body_open].span.start <= wanted
            && wanted <= tokens[source.body_close].span.end;
        let in_grouped_proof = function.grouped_proof().is_some()
            && find_grouped_proof_span(&tokens, &source)?.contains(&wanted);
        if in_body || in_grouped_proof {
            return Ok(VerificationTarget::Function(function_name.to_string()));
        }
    }
    Err(ClickError::new(format!(
        "no theorem or C function proof contains source location {line}:{column}"
    )))
}

/// The diagnostic spellings `describe_pointer` falls back to when a kernel
/// pointer has no source form. None of them is Click syntax, so an expansion
/// that renders one cannot parse; expansion has to say which name it is
/// missing instead of handing the parse error on.
const UNRAISABLE_POINTER_FORMS: [&str; 5] = [
    // The ellipsis `describe_pointer` prints for a heap, temporary or
    // symbolic block no source names.
    "…",
    "symbolic-pointer:",
    "symbolic-function-pointer:",
    "heap-allocation:",
    "arg-memory",
];

/// Reports why a rendered expansion is not Click. A composite resource's
/// existential witness may have no usable source spelling in this scope.
/// When no checked alias names that pointer, report the missing witness
/// name rather than the parse error from diagnostic-only pointer text.
fn unparseable_expansion_error(
    click_source: &str,
    sources: &ProgramSourceContext<'_>,
    replacement: &str,
    parse_error: ClickError,
) -> ClickError {
    let file = parse_source_with_program_layouts_context(click_source, sources).ok();
    unparseable_expansion_error_for_file(replacement, parse_error, file.as_ref())
}

fn unparseable_expansion_error_for_file(
    replacement: &str,
    parse_error: ClickError,
    file: Option<&ClickFile>,
) -> ClickError {
    if parse_error.verification_stopped() {
        return parse_error;
    }
    let fragment: String = replacement.chars().take(400).collect();
    let generated = format!("Generated fragment starts with {fragment:?}");
    if replacement.contains(super::printing::UNRAISED_CONJUNCT) {
        return ClickError::new(format!(
            "the expansion could not raise a checked `all` arm label (report this as a bug)\n{generated}"
        ));
    }
    if !UNRAISABLE_POINTER_FORMS
        .iter()
        .any(|form| replacement.contains(form))
    {
        return parse_error.with_prefix(format!(
            "the expansion did not parse as Click (report this as a bug)\n{generated}\n"
        ));
    }
    let witnesses = file
        .map(|file| {
            file.resource_definitions()
                .iter()
                .filter_map(|definition| {
                    let body = definition.composite_body()?;
                    Some(
                        body.witnesses()
                            .iter()
                            .map(|witness| {
                                format!("`{}` of `{}`", witness.name(), definition.name())
                            })
                            .collect::<Vec<_>>(),
                    )
                })
                .flatten()
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let named = match witnesses.as_slice() {
        [] => "a value the kernel introduced".to_string(),
        [only] => format!("the witness {only}"),
        several => format!("one of the witnesses {}", several.join(", ")),
    };
    ClickError::new(format!(
        "the expansion needs a name for {named}, which has no surface spelling (report this as a bug)\n{generated}"
    ))
}

/// Rejects a rendered expansion that is not Click before it reaches the
/// caller's verification, so the reported failure is the missing name rather
/// than the parse error the unparseable text produces.
fn checked_expanded_source(
    click_source: &str,
    sources: &ProgramSourceContext<'_>,
    replacement: &str,
    expanded: String,
) -> Result<String, ClickError> {
    match parse_source_with_program_layouts_context(&expanded, sources) {
        Ok(_) => Ok(expanded),
        Err(error) => Err(unparseable_expansion_error(
            click_source,
            sources,
            replacement,
            error,
        )),
    }
}

/// Expands one tactic and returns the rewritten source.
///
/// Certificate capture verifies the selected proof prefix. The caller is
/// responsible for verifying the returned sidecar and its proof suffix.
pub fn expand_c_tactic_source_at(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    expand_c_tactic_source_at_context(None, click_source, c_sources, line, column)
}

pub fn expand_project_tactic_source_at(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let project = Some(project);
    match inputs {
        ProgramInputs::Bundle(c_sources) => {
            expand_c_tactic_source_at_context(project, click_source, c_sources, line, column)
        }
        ProgramInputs::Prepared(imports) => {
            expand_c_prepared_tactic_source_at_context(project, click_source, imports, line, column)
        }
        ProgramInputs::Program(import) => expand_program_prepared_tactic_source_at_context(
            project,
            click_source,
            import,
            line,
            column,
        ),
    }
}

fn expand_c_tactic_source_at_context(
    project: Option<&ClickProject>,
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let file = if let Some(project) = project {
        let sources = ProgramSourceContext::bundle(c_sources).with_click_project(project);
        resolve_click_project_context(project, &sources)?
    } else {
        parse_source_with_c_layouts(click_source, c_sources)?
    };
    let selected = locate_source_tactic_file(click_source, &file, line, column)?;
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &selected.site
    {
        return if let Some(project) = project {
            expand_project_pure_theorem_source(
                project,
                &ProgramInputs::Bundle(c_sources.to_vec()),
                theorem_name,
                *ensure_index,
            )
        } else {
            expand_pure_theorem_source(click_source, c_sources, theorem_name, *ensure_index)
        };
    }
    if let (
        ProofSite::FunctionClaim {
            function_name,
            claim,
        },
        TacticSourceEdit::WholeProof(_),
    ) = (&selected.site, &selected.edit)
    {
        return if let Some(project) = project {
            expand_project_claim_source(
                project,
                &ProgramInputs::Bundle(c_sources.to_vec()),
                function_name,
                *claim,
            )
        } else {
            expand_c_claim_source(click_source, c_sources, function_name, *claim)
        };
    }
    let _parameter_places = selected
        .function_block
        .as_ref()
        .map(super::diagnostics::ParameterPlaceScope::enter);
    let replacement_tactics = match &selected.edit {
        TacticSourceEdit::Partial(_)
        | TacticSourceEdit::Append(_)
        | TacticSourceEdit::PartialProofClause(_) => {
            if let Some(project) = project {
                super::proof::capture_project_tactic_expansion(
                    project,
                    &ProgramInputs::Bundle(c_sources.to_vec()),
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            } else {
                super::proof::capture_program_tactic_expansion(
                    click_source,
                    c_sources,
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            }
        }
        TacticSourceEdit::WholeProof(_) => {
            if let Some(project) = project {
                super::proof::capture_project_proof_site_expansion(
                    project,
                    &ProgramInputs::Bundle(c_sources.to_vec()),
                    selected.site.clone(),
                )?
            } else {
                super::proof::capture_program_proof_site_expansion(
                    click_source,
                    c_sources,
                    selected.site.clone(),
                )?
            }
        }
    };
    let (span, replacement) = selected.replacement(click_source, &file, &replacement_tactics)?;
    // A tactic that contributed no step is removed, but a `by { ... }` block
    // must hold at least one tactic. When it is the only tactic of its
    // block, the block keeps `close();`, the step a phase with nothing
    // to prove is checked by.
    let replacement = if replacement.is_empty()
        && click_source[..span.start].trim_end().ends_with('{')
        && click_source[span.end..].trim_start().starts_with('}')
    {
        printing::CLOSE_CALL.to_string()
    } else {
        replacement
    };
    // An empty replacement removes the selected tactic: take its whole line
    // when nothing else shares it, so the rewrite leaves no blank residue.
    let span = if replacement.is_empty() {
        let line_start = click_source[..span.start]
            .rfind('\n')
            .map_or(0, |index| index + 1);
        let line_end = click_source[span.end..]
            .find('\n')
            .map_or(click_source.len(), |index| span.end + index + 1);
        if click_source[line_start..span.start].trim().is_empty()
            && click_source[span.end..line_end].trim().is_empty()
        {
            line_start..line_end
        } else {
            span
        }
    } else {
        span
    };
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let expanded = splice_source(
        click_source,
        &proof_source_tokens(click_source, &selected.source_spans.implicit_proofs)?,
        &span,
        &replacement,
    )?;
    if let Some(project) = project {
        let rewritten = project.with_entry_source(expanded.clone());
        let sources = ProgramSourceContext::bundle(c_sources).with_click_project(&rewritten);
        match resolve_click_project_context(&rewritten, &sources) {
            Ok(_) => Ok(expanded),
            Err(error) => {
                let original_sources =
                    ProgramSourceContext::bundle(c_sources).with_click_project(project);
                let original = resolve_click_project_context(project, &original_sources).ok();
                Err(unparseable_expansion_error_for_file(
                    &replacement,
                    error,
                    original.as_ref(),
                ))
            }
        }
    } else {
        checked_expanded_source(
            click_source,
            &ProgramSourceContext::bundle(c_sources),
            &replacement,
            expanded,
        )
    }
}

/// Expands one tactic using compiler-prepared translation units throughout
/// location, capture, and certificate verification.
pub fn expand_c_prepared_tactic_source_at(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    expand_c_prepared_tactic_source_at_context(None, click_source, imports, line, column)
}

pub fn expand_program_prepared_tactic_source_at(
    click_source: &str,
    import: impl Into<crate::languages::PreparedProgram>,
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    expand_program_prepared_tactic_source_at_context(
        None,
        click_source,
        &import.into(),
        line,
        column,
    )
}

fn expand_program_prepared_tactic_source_at_context(
    project: Option<&ClickProject>,
    click_source: &str,
    import: &crate::languages::PreparedProgram,
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let sources = match project {
        Some(project) => ProgramSourceContext::program(import)?.with_click_project(project),
        None => ProgramSourceContext::program(import)?,
    };
    let file = match project {
        Some(project) => resolve_click_project_context(project, &sources)?,
        None => parse_source_with_program_layouts_context(click_source, &sources)?,
    };
    let selected = locate_source_tactic_file(click_source, &file, line, column)?;
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &selected.site
    {
        let verified = match project {
            Some(project) => verify_click_project_theorem_context(project, &sources, theorem_name)?,
            None => verify_click_theorem_context(click_source, &sources, theorem_name)?,
        };
        return rewrite_verified_pure_theorem(click_source, &verified, theorem_name, *ensure_index);
    }
    if let (
        ProofSite::FunctionClaim {
            function_name,
            claim,
        },
        TacticSourceEdit::WholeProof(_),
    ) = (&selected.site, &selected.edit)
    {
        return match project {
            Some(project) => expand_project_claim_source(
                project,
                &ProgramInputs::program(import),
                function_name,
                *claim,
            ),
            None => expand_program_prepared_claim_source_context(
                click_source,
                import,
                function_name,
                *claim,
            ),
        };
    }
    let block = selected.function_block.as_ref();
    let _reference_result_source = super::diagnostics::ReferenceResultSourceScope::enter(
        block.is_some_and(|block| block.signature().returns_reference()),
    );
    let _parameter_places = block.map(super::diagnostics::ParameterPlaceScope::enter);
    let replacement_tactics = match &selected.edit {
        TacticSourceEdit::Partial(_)
        | TacticSourceEdit::Append(_)
        | TacticSourceEdit::PartialProofClause(_) => {
            if let Some(project) = project {
                super::proof::capture_project_tactic_expansion(
                    project,
                    &ProgramInputs::program(import),
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            } else {
                super::proof::capture_prepared_tactic_expansion(
                    click_source,
                    &sources,
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            }
        }
        TacticSourceEdit::WholeProof(_) => {
            if let Some(project) = project {
                super::proof::capture_project_proof_site_expansion(
                    project,
                    &ProgramInputs::program(import),
                    selected.site.clone(),
                )?
            } else {
                super::proof::capture_prepared_proof_site_expansion(
                    click_source,
                    &sources,
                    selected.site.clone(),
                )?
            }
        }
    };
    let (span, replacement) = selected.replacement(click_source, &file, &replacement_tactics)?;
    let expanded = splice_source(
        click_source,
        &proof_source_tokens(click_source, &selected.source_spans.implicit_proofs)?,
        &span,
        &replacement,
    )?;
    checked_expanded_source(click_source, &sources, &replacement, expanded)
}

fn expand_c_prepared_tactic_source_at_context(
    project: Option<&ClickProject>,
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let sources = ProgramSourceContext::prepared(imports);
    let file = if let Some(project) = project {
        let project_sources = ProgramSourceContext::prepared(imports).with_click_project(project);
        resolve_click_project_context(project, &project_sources)?
    } else {
        parse_source_with_program_layouts_context(click_source, &sources)?
    };
    let selected = locate_source_tactic_file(click_source, &file, line, column)?;
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &selected.site
    {
        return if let Some(project) = project {
            expand_project_pure_theorem_source(
                project,
                &ProgramInputs::Prepared(imports),
                theorem_name,
                *ensure_index,
            )
        } else {
            expand_pure_theorem_source_context(click_source, &sources, theorem_name, *ensure_index)
        };
    }
    if let (
        ProofSite::FunctionClaim {
            function_name,
            claim,
        },
        TacticSourceEdit::WholeProof(_),
    ) = (&selected.site, &selected.edit)
    {
        return if let Some(project) = project {
            expand_project_claim_source(
                project,
                &ProgramInputs::Prepared(imports),
                function_name,
                *claim,
            )
        } else {
            expand_c_prepared_claim_source(click_source, imports, function_name, *claim)
        };
    }
    let _parameter_places = selected
        .function_block
        .as_ref()
        .map(super::diagnostics::ParameterPlaceScope::enter);
    let replacement_tactics = match &selected.edit {
        TacticSourceEdit::Partial(_)
        | TacticSourceEdit::Append(_)
        | TacticSourceEdit::PartialProofClause(_) => {
            if let Some(project) = project {
                super::proof::capture_project_tactic_expansion(
                    project,
                    &ProgramInputs::Prepared(imports),
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            } else {
                super::proof::capture_prepared_tactic_expansion(
                    click_source,
                    &sources,
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            }
        }
        TacticSourceEdit::WholeProof(_) => {
            if let Some(project) = project {
                super::proof::capture_project_proof_site_expansion(
                    project,
                    &ProgramInputs::Prepared(imports),
                    selected.site.clone(),
                )?
            } else {
                super::proof::capture_prepared_proof_site_expansion(
                    click_source,
                    &sources,
                    selected.site.clone(),
                )?
            }
        }
    };
    let (span, replacement) = selected.replacement(click_source, &file, &replacement_tactics)?;
    let expanded = splice_source(
        click_source,
        &proof_source_tokens(click_source, &selected.source_spans.implicit_proofs)?,
        &span,
        &replacement,
    )?;
    if let Some(project) = project {
        let rewritten = project.with_entry_source(expanded.clone());
        let project_sources =
            ProgramSourceContext::prepared(imports).with_click_project(&rewritten);
        match resolve_click_project_context(&rewritten, &project_sources) {
            Ok(_) => Ok(expanded),
            Err(error) => {
                let original_sources =
                    ProgramSourceContext::prepared(imports).with_click_project(project);
                let original = resolve_click_project_context(project, &original_sources).ok();
                Err(unparseable_expansion_error_for_file(
                    &replacement,
                    error,
                    original.as_ref(),
                ))
            }
        }
    } else {
        checked_expanded_source(click_source, &sources, &replacement, expanded)
    }
}

fn expand_pure_theorem_source(
    click_source: &str,
    c_sources: &[(&str, &str)],
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let sources = ProgramSourceContext::bundle(c_sources);
    expand_pure_theorem_source_context(click_source, &sources, theorem_name, ensure_index)
}

fn expand_project_pure_theorem_source(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
    let verified = verify_click_project_theorem_context(project, &sources, theorem_name)?;
    rewrite_verified_pure_theorem(click_source, &verified, theorem_name, ensure_index)
}

fn expand_pure_theorem_source_context(
    click_source: &str,
    sources: &ProgramSourceContext<'_>,
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let verified = verify_click_theorem_context(click_source, sources, theorem_name)?;
    rewrite_verified_pure_theorem(click_source, &verified, theorem_name, ensure_index)
}

fn rewrite_verified_pure_theorem(
    click_source: &str,
    verified: &[VerifiedPureTheorem],
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let theorem = verified
        .iter()
        .find(|theorem| {
            theorem.theorem_definition.name() == theorem_name
                && theorem.ensure_index == ensure_index
        })
        .ok_or_else(|| {
            ClickError::new(format!(
                "verified theorem `{theorem_name}` has no ensure {ensure_index}"
            ))
        })?;
    let tokens = proof_source_tokens(
        click_source,
        &theorem.theorem_definition.parsed_body().implicit_proofs,
    )?;
    let _binder_names = printing::CertificateBinderScope::enter(click_source, []);
    let replacement = theorem.expanded_proof_source()?;
    let source = DeclarationSources::new(&tokens).theorem(&theorem.theorem_definition)?;
    let edit = find_ensure_proof_edit(&tokens, &source, ensure_index)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => {
            unreachable!("theorem ensure edits are never loop phases")
        }
    };
    splice_source(click_source, &tokens, span, &replacement)
}

/// Spells the checked certificate that replaces a whole claim proof.
/// Written nesting is not a driver bound: terminal cases can be processed
/// iteratively. As with tactic expansion, the caller verifies the rewrite.
fn claim_expansion_source(
    click_source: &str,
    theorem: &VerifiedProgramTheorem,
) -> Result<String, ClickError> {
    let _binder_names =
        printing::CertificateBinderScope::enter(click_source, [theorem.function_block.as_ref()]);
    let _contract_value_parameters = theorem.contract_value_parameter_scope();
    let _reference_result_source = super::diagnostics::ReferenceResultSourceScope::enter(
        theorem.function_block.signature().returns_reference(),
    );
    let _reference_carriers =
        super::diagnostics::ParameterPlaceScope::enter(&theorem.function_block);
    let _spelling = theorem.step_result_spelling_scope();
    let certificate = theorem.expanded_proof_certificate()?;
    if !theorem.function_block.is_tactic_procedure() {
        return Ok(super::printing::format_proof_block(
            &sequential_early_returns(
                certificate.to_proof_tactics(),
                theorem.checked_execution.function(),
            ),
        ));
    }
    // A tactic's proof is checked with a fixed ending on every live path: one
    // step over the empty procedure's `return`, then an `known` per
    // claim, followed by the ordinary contract-closing proofs. The ending is
    // supplied by the checker and cannot be written in
    // a tactic's proof, which runs no code, so the expansion leaves it out.
    let mut tactics = certificate.to_proof_tactics();
    let ending = super::verification::tactic_procedure_ending_len(&theorem.function_block);
    remove_tactic_procedure_ending(&mut tactics, ending).map_err(|()| {
        ClickError::new(format!(
            "the expanded proof of tactic `{}` does not end in the step and {} closing known step(s) its check supplies",
            theorem.function_block.signature().name(),
            ending - 1
        ))
    })?;
    Ok(super::printing::format_proof_block(&tactics))
}

/// Spells a whole function proof's early returns one after another.
///
/// A checked certificate nests each early return's continuation in the
/// `else` arm of the proof `if` before it, so `N` sequential returns would
/// print `N` levels deep. At the end of a function proof every arm of an
/// execution `if` reaches function exit. When its `then` arm does, and its
/// `else` arm ends in another execution split, that split is the lone live
/// arm's continuation: it and its preceding non-entry tactics are written
/// after the `if`, where the driver runs them in that arm. Moving the prefix
/// with the split preserves the scope of the names it introduces. Only an
/// `if` whose C then-arm returns from the function is moved. A continuing C
/// arm keeps its nested continuation, as does a post-execution case split.
fn sequential_early_returns(
    tactics: Vec<ProofTactic>,
    function: &ProgramFunction,
) -> Vec<ProofTactic> {
    sequential_early_return_tactics(tactics, &returning_then_arms(function.body()))
}

fn returning_then_arms(statement: &ProgramStatement) -> BTreeSet<usize> {
    // Use the same executable preorder as source statement anchors: sequences
    // add no node; if/while/try visit their bodies; other operations are atomic.
    // Some(false) may fall through; Some(true) returns on every path.
    // None includes a nonlocal transfer, which may bypass a later return.
    fn visit(
        statement: &ProgramStatement,
        index: &mut usize,
        returns: &mut BTreeSet<usize>,
        catches_exceptions: bool,
    ) -> Option<bool> {
        crate::instrumentation::record_deterministic_work(1);
        if let ProgramStatement::Seq(statements) = statement {
            let mut flow = Some(false);
            for statement in statements.iter() {
                let next = visit(statement, index, returns, catches_exceptions);
                if flow == Some(false) {
                    flow = next;
                }
            }
            return flow;
        }
        let head = *index;
        *index += 1;
        match statement {
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_returns = visit(then_branch, index, returns, catches_exceptions);
                let else_returns = visit(else_branch, index, returns, catches_exceptions);
                if then_returns == Some(true) {
                    returns.insert(head);
                }
                then_returns.zip(else_returns).map(|(a, b)| a && b)
            }
            ProgramStatement::Loop {
                test: loop_test,
                update,
                body,
                ..
            } => {
                let test = loop_test.source_region();
                for region in crate::kernel::program_loop_regions(body, update.as_deref(), test) {
                    visit(region, index, returns, catches_exceptions);
                }
                None
            }
            ProgramStatement::TryCatchInt32 {
                try_body, handler, ..
            } => {
                let body_returns = visit(try_body, index, returns, true);
                let handler_returns = visit(handler, index, returns, catches_exceptions);
                body_returns.zip(handler_returns).map(|(a, b)| a && b)
            }
            // Numbered as the source layout numbers it: the body, then the
            // cleanup and the point where the exception continues.
            ProgramStatement::UnwindCleanup { body, cleanup } => {
                let body_returns = visit(body, index, returns, true);
                let unwinding = crate::kernel::program_unwind_continuation(
                    cleanup,
                    crate::kernel::program_expression::int32_literal(0),
                );
                let cleanup_returns = visit(&unwinding, index, returns, catches_exceptions);
                body_returns.zip(cleanup_returns).map(|(a, b)| a && b)
            }
            ProgramStatement::Return(_) => Some(true),
            // A throwing call can resume in the enclosing handler before
            // the return this sequence would otherwise reach.
            ProgramStatement::Call { .. }
            | ProgramStatement::CallConstruct { .. }
            | ProgramStatement::CallResult { .. }
                if catches_exceptions =>
            {
                None
            }
            // A nonlocal transfer can bypass a later return in a sequence.
            // A throw may enter a surrounding handler instead of exiting.
            ProgramStatement::Break
            | ProgramStatement::Continue
            | ProgramStatement::Goto { .. }
            | ProgramStatement::Throw(_)
            | ProgramStatement::Switch { .. } => None,
            _ => Some(false),
        }
    }
    let mut returns = BTreeSet::new();
    visit(statement, &mut 0, &mut returns, false);
    returns
}

fn sequential_early_return_tactics(
    tactics: Vec<ProofTactic>,
    returns: &BTreeSet<usize>,
) -> Vec<ProofTactic> {
    fn steps_c(tactics: &[ProofTactic]) -> bool {
        tactics.iter().any(|tactic| {
            matches!(
                tactic,
                ProofTactic::Step
                    | ProofTactic::StepContract(_)
                    | ProofTactic::StepBind(_)
                    | ProofTactic::StepCall(_)
                    | ProofTactic::StepProved { .. }
            )
        })
    }
    fn continues_after_return(proof_if: &ProofIf, returns: &BTreeSet<usize>) -> bool {
        let early_return = matches!(
            super::proof::surface_program_point_selector(&proof_if.condition),
            Some(ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Region(index), kind: ProgramPointKind::Entry,
            })) if returns.contains(&index)
        );
        early_return
            && proof_if.ensuring.is_none()
            && steps_c(&proof_if.then_tactics)
            && proof_if.else_tactics.len() >= 2
            && matches!(proof_if.else_tactics.first(), Some(ProofTactic::Step))
            && matches!(
                proof_if.else_tactics.last(),
                Some(ProofTactic::If(tail))
                    if tail.ensuring.is_none()
                        && (steps_c(&tail.then_tactics) || steps_c(&tail.else_tactics))
            )
    }
    let mut flat = Vec::with_capacity(tactics.len());
    let mut rest = tactics;
    loop {
        let Some(ProofTactic::If(proof_if)) = rest.last() else {
            flat.append(&mut rest);
            return flat;
        };
        if !continues_after_return(proof_if, returns) {
            flat.append(&mut rest);
            return flat;
        }
        let Some(ProofTactic::If(mut proof_if)) = rest.pop() else {
            unreachable!("the last tactic is the proof `if` just inspected")
        };
        // Keep the C split's entry operations in its arm, and move the
        // remaining prefix together with the next split. Names bound by
        // that prefix must stay in scope throughout their continuation.
        let entry_steps = proof_if
            .else_tactics
            .iter()
            .take_while(|tactic| matches!(tactic, ProofTactic::Step))
            .count();
        let continuation = proof_if.else_tactics.split_off(entry_steps);
        // The `then` arm ends at function exit too, so its own returns
        // flatten the same way; its nesting is not the chain's length.
        proof_if.then_tactics =
            sequential_early_return_tactics(std::mem::take(&mut proof_if.then_tactics), returns);
        flat.append(&mut rest);
        flat.push(ProofTactic::If(proof_if));
        rest = continuation;
    }
}

/// Removes the `ending` tactics the checker appends where each path of a
/// tactic's proof ends: at the end of the script, or of each arm of a final
/// proof `match`. A refuted path has no supplied ending.
fn remove_tactic_procedure_ending(tactics: &mut Vec<ProofTactic>, ending: usize) -> Result<(), ()> {
    if matches!(tactics.last(), Some(ProofTactic::Contradiction(_))) {
        return Ok(());
    }
    if let Some(ProofTactic::Match(proof_match)) = tactics.last_mut() {
        for arm in &mut std::sync::Arc::make_mut(proof_match).arms {
            remove_tactic_procedure_ending(&mut arm.tactics, ending)?;
        }
        return Ok(());
    }
    let kept = tactics.len().checked_sub(ending).ok_or(())?;
    let supplied = matches!(tactics[kept], ProofTactic::Step)
        && tactics[kept + 1..]
            .iter()
            .all(|tactic| matches!(tactic, ProofTactic::Known));
    if !supplied {
        return Err(());
    }
    tactics.truncate(kept);
    Ok(())
}

fn select_expansion_theorem<'a>(
    verified: &'a [VerifiedProgramTheorem],
    function_name: &str,
    claim: ContractProofClaim,
) -> Result<&'a VerifiedProgramTheorem, ClickError> {
    let matches_function = |theorem: &&VerifiedProgramTheorem| {
        theorem.function_block.signature().name() == function_name
    };
    let selected = match claim {
        ContractProofClaim::Ensure(index) => verified.iter().find(|theorem| {
            matches_function(theorem)
                && matches!(theorem.claim, VerifiedClaim::Ensure { index: found, .. } if found == index)
        }),
        ContractProofClaim::ExceptionalEnsure(index) => verified.iter().find(|theorem| {
            matches_function(theorem)
                && matches!(theorem.claim, VerifiedClaim::ExceptionalEnsure { index: found, .. } if found == index)
        }),
        ContractProofClaim::Grouped => verified
            .iter()
            .find(|theorem| {
                matches_function(theorem)
                    && match &theorem.claim {
                        VerifiedClaim::Ensure { clause, .. }
                        | VerifiedClaim::ExceptionalEnsure { clause, .. } => {
                            theorem.function_block.covers_claim_proof(clause.proof())
                        }
                    }
            })
            .or_else(|| verified.iter().find(matches_function)),
    };
    selected.ok_or_else(|| {
        ClickError::new(format!(
            "verified function `{function_name}` has no verified {}",
            claim.describe()
        ))
    })
}

use super::parser::SourceToken;

#[derive(Clone)]
struct FunctionSource {
    body_open: usize,
    body_close: usize,
    /// The first token of each written claim clause, where the parser read
    /// it, in source order, with the proof clause the parser read for it.
    clauses: Vec<Option<(usize, parsed_blocks::ProofClause)>>,
    /// The `exceptional` token of each `exceptional ensures` clause, with
    /// its proof clause.
    exceptional: Vec<Option<(usize, parsed_blocks::ProofClause)>>,
    /// The grouped proof after the clauses' closing brace.
    grouped: Option<parsed_blocks::ProofClause>,
}

/// Finds the bodies the parser recorded for declarations among the tokens
/// of the source it read. Each token carries the position the parser gives
/// it, so a recorded position is one binary search among the tokens and no
/// source text is read.
struct DeclarationSources<'a> {
    tokens: &'a [SourceToken],
}

impl<'a> DeclarationSources<'a> {
    fn new(tokens: &'a [SourceToken]) -> Self {
        Self { tokens }
    }

    /// The written token at `position`, when `text` is given the one with
    /// that text. An implicit proof block's zero-width brace can share a
    /// token's start, so the written token is chosen among the tokens there.
    fn token_at(&self, position: &SourcePosition, text: Option<&str>) -> Option<usize> {
        let key = (position.line, position.column);
        crate::instrumentation::record_deterministic_work(1);
        let first = self
            .tokens
            .partition_point(|token| (token.start.line, token.start.column) < key);
        self.tokens[first..]
            .iter()
            .take_while(|token| (token.start.line, token.start.column) == key)
            .position(|token| text.is_none_or(|text| token.text == text) && !token.span.is_empty())
            .map(|found| first + found)
    }

    /// The braces around the clauses of the declaration `name`: the one the
    /// parser read them from, and the brace that closes it.
    fn body(
        &self,
        name: &str,
        body: &parser::DeclarationBody,
    ) -> Result<FunctionSource, ClickError> {
        let open = body
            .open
            .as_ref()
            .ok_or_else(|| ClickError::new(format!("`{name}` was not read from source text")))?;
        let missing = || ClickError::new(format!("could not locate the source of `{name}`"));
        let body_open = self.token_at(open, Some("{")).ok_or_else(missing)?;
        let body_close = body
            .close
            .as_ref()
            .and_then(|close| self.token_at(close, Some("}")))
            .ok_or_else(missing)?;
        let proofs = parsed_blocks::ProofClauses::new(self.tokens, &body.proof_clauses);
        // A claim's proof is the first clause after it: nothing a claim
        // states holds a proof of its own.
        let with_proof = |clauses: &[Option<SourcePosition>]| {
            clauses
                .iter()
                .map(|clause| {
                    let clause = self.token_at(clause.as_ref()?, None)?;
                    Some((clause, proofs.after(clause, body_close).ok()?))
                })
                .collect()
        };
        Ok(FunctionSource {
            body_open,
            body_close,
            clauses: with_proof(&body.clauses),
            exceptional: with_proof(&body.exceptional_clauses),
            grouped: proofs.at(body_close + 1).ok(),
        })
    }

    fn function(&self, block: &FunctionBlock) -> Result<FunctionSource, ClickError> {
        self.body(block.signature().name(), block.parsed_body())
    }

    fn theorem(&self, theorem: &TheoremDefinition) -> Result<FunctionSource, ClickError> {
        self.body(theorem.name(), theorem.parsed_body())
    }
}

/// A source's tokens with the proof blocks the parser read in them. It reads
/// as the token slice it wraps.
struct ProofTokens<'a> {
    tokens: &'a [SourceToken],
    blocks: Arc<parsed_blocks::ParsedBlocks>,
    /// The parse these blocks come from.
    spans: Arc<parser::SourceSpans>,
}

impl<'a> ProofTokens<'a> {
    fn new(file: &ClickFile, tokens: &'a [SourceToken]) -> Self {
        Self {
            tokens,
            blocks: Arc::new(parsed_blocks::ParsedBlocks::new(
                tokens,
                file.source_spans(),
            )),
            spans: file.source_spans().clone(),
        }
    }

    /// The `}` of the proof block whose `{` is `with`.
    fn block_close(&self, open: usize) -> Result<usize, ClickError> {
        Ok(self.blocks.block(open)?.close)
    }

    /// The token ranges of the tactics in the block `open..=close`.
    fn tactic_ranges(&self, open: usize, _close: usize) -> Result<Vec<Range<usize>>, ClickError> {
        Ok(self.blocks.block(open)?.tactics.clone())
    }

    fn child_blocks(&self, range: &Range<usize>) -> Vec<(usize, usize)> {
        self.blocks.child_blocks(range)
    }

    fn two_arms(
        &self,
        range: &Range<usize>,
        kind: &str,
    ) -> Result<[(usize, usize); 2], ClickError> {
        self.blocks.two_arms(range, kind)
    }

    fn cases_arms(&self, range: &Range<usize>) -> Result<Vec<(usize, usize)>, ClickError> {
        self.blocks.cases_arms(range)
    }

    fn labeled_arms(
        &self,
        range: &Range<usize>,
        labels: [&str; 2],
    ) -> Result<[(usize, usize); 2], ClickError> {
        self.blocks.labeled_arms(self.tokens, range, labels)
    }

    fn body_block(&self, range: &Range<usize>, kind: &str) -> Result<(usize, usize), ClickError> {
        self.blocks.body_block(range, kind)
    }

    /// The `phase` proof clause of the `loop` tactic `range`: the clause the
    /// parser read after the loop's own `phase` keyword, not one in a proof
    /// nested inside the loop.
    fn loop_phase(
        &self,
        range: &Range<usize>,
        phase: &str,
    ) -> Option<(usize, parsed_blocks::ProofClause)> {
        let nested = self.blocks.child_blocks(range);
        self.blocks
            .clauses
            .owned_in(range.start + 1..range.end)
            .find(|&(owner, _)| {
                self.tokens[owner].text == phase
                    && !nested
                        .iter()
                        .any(|&(open, close)| open < owner && owner < close)
            })
    }
}

impl std::ops::Deref for ProofTokens<'_> {
    type Target = [SourceToken];

    fn deref(&self) -> &[SourceToken] {
        self.tokens
    }
}

/// A source's tokens, with no proof blocks supplied: for scans of its
/// headers and of explicit braces only.
fn plain_source_tokens(source: &str) -> Result<Vec<SourceToken>, ClickError> {
    source_index::record_tokenization_work(source.len());
    parser::source_tokens(source)
}

/// A source's tokens with the implicit proof blocks its parse recorded: a
/// file's, or those of the one declaration a caller edits.
fn proof_source_tokens(
    source: &str,
    implicit: &[parser::ImplicitProofSpan],
) -> Result<Vec<SourceToken>, ClickError> {
    Ok(with_implicit_proof_blocks(
        plain_source_tokens(source)?,
        implicit,
    ))
}

/// A proof written as one tactic, `by T(args);`, is the block
/// `by { T(args); }` without its braces. Every reader below addresses a
/// proof's tactics through the block that holds them, so the parser's record
/// of each such tactic supplies the missing pair as zero-width tokens at the
/// tactic's two ends. Their spans are exact source positions, and
/// [`splice_source`] writes the braces out whenever a rewrite lands inside
/// one. A record whose tokens are not in `tokens` adds no block.
fn with_implicit_proof_blocks(
    tokens: Vec<SourceToken>,
    implicit: &[parser::ImplicitProofSpan],
) -> Vec<SourceToken> {
    if implicit.is_empty() {
        return tokens;
    }
    let by_position = tokens
        .iter()
        .enumerate()
        .map(|(index, token)| ((token.start.line, token.start.column), index))
        .collect::<std::collections::HashMap<_, _>>();
    let mut opens = vec![0_usize; tokens.len()];
    let mut closes = vec![0_usize; tokens.len()];
    // A tactic the parser read twice, on a path it backtracked from, is
    // still one block.
    let mut blocks = std::collections::HashSet::new();
    for span in implicit {
        let (Some(&first), Some(&last)) = (
            by_position.get(&(span.first.line, span.first.column)),
            by_position.get(&(span.last.line, span.last.column)),
        ) else {
            continue;
        };
        if first <= last && blocks.insert((first, last)) {
            opens[first] += 1;
            closes[last] += 1;
        }
    }
    let added = opens.iter().sum::<usize>() * 2;
    let mut blocked = Vec::with_capacity(tokens.len() + added);
    for (index, token) in tokens.into_iter().enumerate() {
        for _ in 0..opens[index] {
            blocked.push(SourceToken {
                text: "{".to_string(),
                span: token.span.start..token.span.start,
                start: token.start.clone(),
            });
        }
        let close = token.span.end;
        let close_position = SourcePosition::new(
            token.start.line,
            token.start.column + token.text.chars().count(),
        );
        blocked.push(token);
        for _ in 0..closes[index] {
            blocked.push(SourceToken {
                text: "}".to_string(),
                span: close..close,
                start: close_position.clone(),
            });
        }
    }
    blocked
}

/// `source` with `span` replaced by `replacement`. A span inside an implicit
/// proof block (see [`with_implicit_proof_blocks`]) gets that block's braces
/// written out, since the replacement may be more than one tactic.
fn splice_source(
    source: &str,
    tokens: &[SourceToken],
    span: &Range<usize>,
    replacement: &str,
) -> Result<String, ClickError> {
    let replacement = require_surface_expansion(printing::spell_source_names(source, replacement))?;
    let replacement = replacement.as_str();
    let mut open_blocks = Vec::new();
    let mut enclosing: Option<Range<usize>> = None;
    for token in tokens.iter().filter(|token| token.span.is_empty()) {
        if token.text == "{" {
            open_blocks.push(token.span.start);
        } else if let Some(open) = open_blocks.pop()
            && open <= span.start
            && span.end <= token.span.start
            && enclosing
                .as_ref()
                .is_none_or(|outer| outer.start <= open && token.span.start <= outer.end)
        {
            // Blocks close innermost first, so the first match is the
            // innermost and later, wider ones are skipped.
            if enclosing.is_none() {
                enclosing = Some(open..token.span.start);
            }
        }
    }
    let whole_block_rewritten_as_a_block = enclosing.as_ref().is_some_and(|block| {
        block.start == span.start
            && block.end == span.end
            && replacement.trim_start().starts_with('{')
    });
    let mut spliced = String::with_capacity(source.len() + replacement.len() + 4);
    match enclosing {
        Some(block) if !whole_block_rewritten_as_a_block => {
            spliced.push_str(&source[..block.start]);
            spliced.push_str("{ ");
            spliced.push_str(&source[block.start..span.start]);
            spliced.push_str(replacement);
            spliced.push_str(&source[span.end..block.end]);
            spliced.push_str(" }");
            spliced.push_str(&source[block.end..]);
        }
        _ => {
            spliced.push_str(&source[..span.start]);
            spliced.push_str(replacement);
            spliced.push_str(&source[span.end..]);
        }
    }
    Ok(with_cited_library_imports(spliced, replacement, source))
}

/// `source` with an `import click::...;` line for each Click library module
/// whose theorem `replacement` cites but `source` does not yet see. A
/// tactic's expansion writes out the library theorems the tactic applied,
/// and the expanded sidecar must still name their modules.
fn with_cited_library_imports(source: String, replacement: &str, original: &str) -> String {
    let cited = replacement
        .split(|character: char| !(character.is_alphanumeric() || character == '_'))
        .filter(|word| !word.is_empty());
    let mut imported = names::SymbolTable::for_source(&source)
        .map(|symbols| symbols.visible_modules())
        .unwrap_or_default();
    imported.extend(
        parser::library_path_modules(&source)
            .unwrap_or_default()
            .into_iter()
            .map(str::to_owned),
    );
    let mut missing = validation::library_modules_to_import(&imported, cited);
    // Preserve dependencies contributed by fully qualified resource paths
    // even when the replacement uses the resource's canonical bare name.
    for module in parser::library_path_modules(original).unwrap_or_default() {
        if !imported.iter().any(|import| import == module) && !missing.contains(&module) {
            missing.push(module);
        }
    }
    if missing.is_empty() {
        return source;
    }
    let mut expanded = missing
        .iter()
        .map(|identity| {
            format!(
                "import {};\n",
                crate::surface::library_module_path(identity)
            )
        })
        .collect::<String>();
    expanded.push_str(&source);
    expanded
}

/// Every block whose proof the expansion tools address: the C function
/// blocks, then each user-defined tactic, whose `by` script is its contract's
/// one grouped proof. A tactic is declared before any proof applies it, so
/// [`find_function`] reaches its declaration first.
fn proof_function_blocks(file: &ClickFile) -> impl Iterator<Item = &FunctionBlock> {
    file.function_blocks()
        .iter()
        .chain(
            file.tactic_definitions()
                .iter()
                .map(TacticDefinition::function_block),
        )
        .filter(|block| file.function_is_selected(block.signature().name()))
        // An `extern` declaration has no proof, and a synthesized one, such
        // as a trait object's pack, has no source text.
        .filter(|block| !block.is_external())
}

fn rust_path_ending_at(tokens: &[SourceToken], end: usize) -> Vec<&str> {
    let mut segments = vec![tokens[end].text.as_str()];
    let mut at = end;
    // The parser retains the path separator as one token.
    while at >= 2 && tokens[at - 1].text == "::" {
        segments.insert(0, tokens[at - 2].text.as_str());
        at -= 2;
    }
    segments
}

fn find_ensure_proof_edit(
    tokens: &[SourceToken],
    source: &FunctionSource,
    wanted: usize,
) -> Result<ProofSourceEdit, ClickError> {
    let (clause, proof) = written_clause(source, wanted)?;
    Ok(claim_proof_edit(tokens, clause, proof))
}

/// The first token of written `ensures`, `owns` or `produces` clause
/// `wanted`, counted together in source order, with its proof clause, as
/// the parser read them.
fn written_clause(
    source: &FunctionSource,
    wanted: usize,
) -> Result<(usize, parsed_blocks::ProofClause), ClickError> {
    source
        .clauses
        .get(wanted)
        .copied()
        .flatten()
        .ok_or_else(|| ClickError::new(format!("could not locate source ensure {wanted}")))
}

/// The `exceptional` token of written `exceptional ensures` clause `wanted`,
/// with its proof clause.
fn written_exceptional_clause(
    source: &FunctionSource,
    wanted: usize,
) -> Result<(usize, parsed_blocks::ProofClause), ClickError> {
    source
        .exceptional
        .get(wanted)
        .copied()
        .flatten()
        .ok_or_else(|| {
            ClickError::new(format!(
                "could not locate source exceptional ensure {wanted}"
            ))
        })
}

fn find_exceptional_ensure_proof_edit(
    tokens: &[SourceToken],
    source: &FunctionSource,
    wanted: usize,
) -> Result<ProofSourceEdit, ClickError> {
    let (clause, proof) = written_exceptional_clause(source, wanted)?;
    // The clause is selected at its `ensures`, after `exceptional`.
    Ok(claim_proof_edit(tokens, clause + 1, proof))
}

/// The edit of the proof clause `proof` of the claim whose first token is
/// `clause`: its whole written `by`, or the `;` of a default proof, selected
/// at the claim.
fn claim_proof_edit(
    tokens: &[SourceToken],
    clause: usize,
    proof: parsed_blocks::ProofClause,
) -> ProofSourceEdit {
    if proof.is_default(tokens) {
        ProofSourceEdit::DefaultTerminator {
            span: tokens[proof.start].span.clone(),
            selector: tokens[clause].span.start,
        }
    } else {
        ProofSourceEdit::Explicit(proof.span(tokens))
    }
}

/// A claim without its own `by` is proved by the function's covering proof,
/// so selecting it selects that grouped proof.
fn covering_claim(function_block: &FunctionBlock, claim: ContractProofClaim) -> ContractProofClaim {
    let clause = match claim {
        ContractProofClaim::Grouped => return claim,
        ContractProofClaim::Ensure(index) => function_block.ensures().get(index),
        ContractProofClaim::ExceptionalEnsure(index) => {
            function_block.exceptional_ensures().get(index)
        }
    };
    if clause.is_some_and(|clause| function_block.covers_claim_proof(clause.proof())) {
        ContractProofClaim::Grouped
    } else {
        claim
    }
}

/// The written grouped proof's span, or, for the implicit `solve` that
/// covers omitted claim proofs, an insertion after the contract block.
fn find_grouped_proof_edit(
    tokens: &[SourceToken],
    function: &FunctionSource,
    function_block: &FunctionBlock,
) -> Result<ProofSourceEdit, ClickError> {
    if function_block.grouped_proof().is_some()
        || expansion_covering_proof(function_block).is_none()
    {
        return Ok(ProofSourceEdit::Explicit(find_grouped_proof_span(
            tokens, function,
        )?));
    }
    let close = &tokens[function.body_close].span;
    Ok(ProofSourceEdit::DefaultTerminator {
        span: close.end..close.end,
        selector: close.start,
    })
}

fn find_grouped_proof_span(
    tokens: &[SourceToken],
    function: &FunctionSource,
) -> Result<Range<usize>, ClickError> {
    function
        .grouped
        .map(|proof| proof.span(tokens))
        .ok_or_else(|| {
            ClickError::new("function uses grouped verification but has no source `by` clause")
        })
}

fn find_claim_proof_span(
    tokens: &[SourceToken],
    function: &FunctionSource,
    function_block: &FunctionBlock,
    claim: ContractProofClaim,
) -> Result<Range<usize>, ClickError> {
    match find_claim_proof_edit(tokens, function, function_block, claim)? {
        ProofSourceEdit::Explicit(span) => Ok(span),
        ProofSourceEdit::DefaultTerminator { .. } => Err(ClickError::new(format!(
            "selected {} uses a default proof and has no explicit source tactic",
            claim.describe()
        ))),
        ProofSourceEdit::OmittedLoopPhase { .. } => {
            unreachable!("function claim edits are never loop phases")
        }
    }
}

#[derive(Clone, Debug)]
enum ProofSourceEdit {
    Explicit(Range<usize>),
    DefaultTerminator {
        span: Range<usize>,
        selector: usize,
    },
    OmittedLoopPhase {
        span: Range<usize>,
        selector: usize,
        phase: &'static str,
    },
}

impl ProofSourceEdit {
    fn span(&self) -> &Range<usize> {
        match self {
            Self::Explicit(span)
            | Self::DefaultTerminator { span, .. }
            | Self::OmittedLoopPhase { span, .. } => span,
        }
    }

    fn selector(&self) -> usize {
        match self {
            Self::Explicit(span) => span.start,
            Self::DefaultTerminator { selector, .. } | Self::OmittedLoopPhase { selector, .. } => {
                *selector
            }
        }
    }
}

fn find_claim_proof_edit(
    tokens: &[SourceToken],
    function: &FunctionSource,
    function_block: &FunctionBlock,
    claim: ContractProofClaim,
) -> Result<ProofSourceEdit, ClickError> {
    match claim {
        // The source is searched by written clause; a flattened aggregate
        // clause gives several ensures one written clause.
        ContractProofClaim::Ensure(index) => {
            find_ensure_proof_edit(tokens, function, function_block.ensure_source_clause(index))
        }
        ContractProofClaim::ExceptionalEnsure(index) => {
            find_exceptional_ensure_proof_edit(tokens, function, index)
        }
        ContractProofClaim::Grouped => Err(ClickError::new(format!(
            "could not locate the source clause for the {}",
            claim.describe()
        ))),
    }
}

/// An explicit expansion request threaded through one verification run.
///
/// Verification fills in `result` for the selected proof site as it goes;
/// nothing about verification's own control flow or execution state depends on
/// the capture being present. This replaces the old thread-local expansion
/// probe and its abort-by-sentinel-error protocol: expansion is now one
/// ordinary verification plus a lookup.
#[derive(Clone, Debug)]
pub(super) struct ExpansionCapture {
    pub(super) site: ProofSite,
    /// `Some` selects one source tactic; `None` requests the whole proof at
    /// the site.
    pub(super) source_index: Option<usize>,
    /// The selected occurrence has been reached; used to route sibling-branch
    /// and deferred finalization bookkeeping for the same occurrence.
    pub(super) active: bool,
    /// First completed capture wins; site-certificate recorders additionally
    /// require agreement across proof obligations.
    pub(super) result: Option<Result<Vec<ProofTactic>, String>>,
    /// The selected occurrence was found inside a C branch arm the kernel
    /// proved infeasible, so checked execution dropped that arm without
    /// running the tactic. This is the fallback answer only: an occurrence
    /// that also runs on a feasible path fills in `result` and that wins.
    pub(super) dropped_path_occurrence: bool,
    /// A selected tactic written inside the body of the `have` at
    /// `source_index` (possibly in an `if` or `cases` arm there), which the
    /// flat source numbering does not reach.
    /// `source_index` still names that enclosing `have`, so the ordinary
    /// occurrence bookkeeping runs unchanged; the answer is the nested
    /// tactic's own checked delta recorded here.
    pub(super) nested: Option<Arc<NestedTacticCapture>>,
    pub(super) replaces_from: Option<usize>,
    /// A partial selection shares one verification. Persistent recorder state
    /// keeps speculative driver clones independent without copying all sites.
    pub(super) batch: Option<Box<BatchExpansionCapture>>,
}

#[derive(Clone, Debug)]
pub(super) struct BatchExpansionCapture {
    pub(super) targets: imbl::OrdMap<usize, ExpansionCapture>,
    pub(super) active_source: Option<usize>,
}

impl ExpansionCapture {
    /// Fork presentation recorders, including nested sites, for one loop-entry path.
    pub(super) fn fork_loop_entry(&self) -> Self {
        self.fork_loop_entry_with(&mut BTreeMap::new())
    }

    fn fork_loop_entry_with(
        &self,
        recorders: &mut BTreeMap<Vec<usize>, Arc<NestedTacticCapture>>,
    ) -> Self {
        let mut result = self.clone();
        result.nested = self
            .nested
            .as_ref()
            .map(|nested| nested.fork_loop_entry(recorders));
        if let Some(batch) = &mut result.batch {
            batch.targets = batch
                .targets
                .iter()
                .map(|(index, target)| (*index, target.fork_loop_entry_with(recorders)))
                .collect();
        }
        result
    }

    pub(super) fn merge_loop_entries(&mut self, paths: &[&Self], branches: &LoopEntryBranches) {
        if self.result.is_none() {
            self.result = guarded_entry_expansion(
                branches,
                &paths
                    .iter()
                    .map(|capture| capture.result.clone())
                    .collect::<Vec<_>>(),
            );
            self.active |= paths.iter().any(|capture| capture.active);
            self.dropped_path_occurrence |=
                paths.iter().any(|capture| capture.dropped_path_occurrence);
            let starts = paths
                .iter()
                .filter_map(|capture| capture.replaces_from)
                .collect::<Vec<_>>();
            if let Some(start) = starts.first() {
                if starts.iter().all(|other| other == start) {
                    self.replaces_from = Some(*start);
                } else {
                    self.result = Some(Err(
                        "loop-entry expansions replace different source ranges".into(),
                    ));
                }
            }
        }
        if let Some(nested) = &self.nested {
            let children = paths
                .iter()
                .map(|capture| {
                    capture
                        .nested
                        .as_ref()
                        .expect("forked nested recorder")
                        .as_ref()
                })
                .collect::<Vec<_>>();
            nested.merge_loop_entries(&children, branches);
        }
        if let Some(batch) = &mut self.batch {
            batch.targets = batch
                .targets
                .iter()
                .map(|(index, target)| {
                    let mut target = target.clone();
                    let children = paths
                        .iter()
                        .map(|capture| {
                            capture
                                .batch
                                .as_ref()
                                .expect("forked batch")
                                .targets
                                .get(index)
                                .expect("forked target")
                        })
                        .collect::<Vec<_>>();
                    target.merge_loop_entries(&children, branches);
                    (*index, target)
                })
                .collect();
        }
    }

    pub(super) fn for_tactic(site: ProofSite, source_index: usize) -> Self {
        Self {
            site,
            source_index: Some(source_index),
            active: false,
            result: None,
            dropped_path_occurrence: false,
            nested: None,
            batch: None,
            replaces_from: None,
        }
    }

    /// Selects the tactic at `nested_path` below the claim-level tactic at
    /// `source_index`, spelled as a proof step's source path continues: one
    /// written position inside each `have` body, and an arm then a written
    /// position inside each `if` or `cases` arm. An empty path selects the
    /// claim-level tactic itself.
    pub(super) fn for_nested_tactic(
        site: ProofSite,
        source_index: usize,
        nested_path: &[usize],
    ) -> Self {
        let mut capture = Self::for_tactic(site.clone(), source_index);
        if !nested_path.is_empty() {
            let mut path = Vec::with_capacity(nested_path.len() + 1);
            path.push(source_index);
            path.extend_from_slice(nested_path);
            capture.nested = Some(Arc::new(NestedTacticCapture::new(site, path)));
        }
        capture
    }

    pub(super) fn for_site(site: ProofSite) -> Self {
        Self {
            site,
            source_index: None,
            active: false,
            result: None,
            dropped_path_occurrence: false,
            nested: None,
            batch: None,
            replaces_from: None,
        }
    }

    pub(super) fn for_tactics(site: ProofSite, targets: &[(usize, Vec<usize>)]) -> Self {
        let mut capture = Self::for_site(site.clone());
        let mut grouped = BTreeMap::<usize, Vec<Vec<usize>>>::new();
        for (index, path) in targets {
            grouped.entry(*index).or_default().push(path.clone());
        }
        let mut nested = BTreeMap::new();
        let targets = grouped
            .into_iter()
            .map(|(index, paths)| {
                let mut target = Self::for_tactic(site.clone(), index);
                let mut children = BTreeMap::new();
                for path in paths.into_iter().filter(|path| !path.is_empty()) {
                    let mut full = vec![index];
                    full.extend(path);
                    let recorder = Arc::new(NestedTacticCapture::new(site.clone(), full.clone()));
                    children.insert(full.clone(), recorder.clone());
                    nested.insert(full, recorder);
                }
                if !children.is_empty() {
                    target.nested = Some(Arc::new(NestedTacticCapture::collection(
                        site.clone(),
                        children,
                    )));
                }
                (index, target)
            })
            .collect();
        capture.batch = Some(Box::new(BatchExpansionCapture {
            targets,
            active_source: None,
        }));
        if !nested.is_empty() {
            capture.nested = Some(Arc::new(NestedTacticCapture::collection(site, nested)));
        }
        capture
    }

    pub(super) fn selects(&self, site: &ProofSite, index: usize) -> bool {
        self.site == *site
            && self
                .batch
                .as_ref()
                .map_or(self.source_index == Some(index), |batch| {
                    batch.targets.contains_key(&index)
                })
    }

    pub(super) fn target_mut(&mut self, index: usize) -> Option<&mut Self> {
        if self.batch.is_some() {
            self.batch.as_mut()?.targets.get_mut(&index)
        } else if self.source_index == Some(index) {
            Some(self)
        } else {
            None
        }
    }

    pub(super) fn active_target_mut(&mut self) -> Option<&mut Self> {
        if self.batch.is_some() {
            let batch = self.batch.as_mut()?;
            batch.targets.get_mut(&batch.active_source?)
        } else {
            Some(self)
        }
    }

    /// The nested-tactic recorder that proofs checking `site` carry, if this
    /// capture selects a tactic inside a `have` body of that proof.
    pub(super) fn nested_for_site(
        &self,
        site: Option<&ProofSite>,
    ) -> Option<Arc<NestedTacticCapture>> {
        self.nested
            .as_ref()
            .filter(|nested| site == Some(&nested.site))
            .cloned()
    }
}

/// The same checked entry decisions organize retained proofs and selected expansions.
pub(super) enum LoopEntryBranches {
    Leaf(Vec<usize>),
    Split {
        condition: ClickProposition,
        yes: Box<Self>,
        no: Box<Self>,
    },
}

impl LoopEntryBranches {
    pub(super) fn certificate(
        &self,
        paths: &[ProofCertificate],
        claim: &str,
    ) -> Result<ProofCertificate, ClickError> {
        crate::instrumentation::record_deterministic_work(1);
        match self {
            Self::Leaf(indices) => {
                let first = indices
                    .first()
                    .ok_or_else(|| ClickError::new("loop preservation has no entry paths"))?;
                for index in &indices[1..] {
                    crate::instrumentation::record_deterministic_work(paths[*index].steps().len());
                    if paths[*index] != paths[*first] {
                        return Err(ClickError::new(format!(
                            "`{claim}` produced different certificates for the same proof path"
                        )));
                    }
                }
                Ok(paths[*first].clone())
            }
            Self::Split { condition, yes, no } => Ok(ProofCertificate::from_validated_steps(vec![
                ProofStep::If {
                    condition: condition.clone(),
                    ensuring: None,
                    then_proof: Box::new(yes.certificate(paths, claim)?),
                    else_proof: Box::new(no.certificate(paths, claim)?),
                },
            ])),
        }
    }
}

fn guarded_entry_expansion(
    branches: &LoopEntryBranches,
    paths: &[Option<Result<Vec<ProofTactic>, String>>],
) -> Option<Result<Vec<ProofTactic>, String>> {
    crate::instrumentation::record_deterministic_work(1);
    match branches {
        LoopEntryBranches::Leaf(indices) => {
            let mut result = None;
            for index in indices {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(next) = &paths[*index] {
                    if result.as_ref().is_some_and(|previous| previous != next) {
                        return Some(Err(
                            "selected tactic expands differently on indistinguishable loop entries"
                                .into(),
                        ));
                    }
                    result = Some(next.clone());
                }
            }
            result
        }
        LoopEntryBranches::Split { condition, yes, no } => {
            let yes = guarded_entry_expansion(yes, paths);
            let no = guarded_entry_expansion(no, paths);
            if yes == no {
                return yes;
            }
            Some((|| {
                Ok(vec![ProofTactic::If(ProofIf {
                    condition: condition.clone(),
                    ensuring: None,
                    then_tactics: yes.transpose()?.unwrap_or_default(),
                    else_tactics: no.transpose()?.unwrap_or_default(),
                })])
            })())
        }
    }
}

/// The recorder for one selected tactic written inside a `have` body.
///
/// Proofs checking the selected site carry it in their shared constants. The
/// linear body runner compares each written tactic's source path with `path`
/// and records the checked certificate delta of the matching tactic. It is
/// presentation metadata only: recording never changes what a step checks.
#[derive(Debug)]
pub(in crate::surface) struct NestedTacticCapture {
    pub(in crate::surface) site: ProofSite,
    /// The selected tactic's source path: the claim-level source index of
    /// the outermost enclosing `have`, then the written position inside each
    /// nested `have` body, or the arm and the written position inside each
    /// `if` or `cases` arm.
    pub(in crate::surface) path: Vec<usize>,
    state: std::sync::Mutex<NestedTacticCaptureState>,
    children: BTreeMap<Vec<usize>, Arc<NestedTacticCapture>>,
}

#[derive(Clone, Debug, Default)]
struct NestedTacticCaptureState {
    /// The selected tactic is being checked now. A smart closure run inside
    /// it addresses its generated steps by the same block positions, so no
    /// inner occurrence may claim the recorder while the outer one holds it.
    active: bool,
    result: Option<Result<Vec<ProofTactic>, String>>,
}

impl NestedTacticCapture {
    fn fork_loop_entry(&self, recorders: &mut BTreeMap<Vec<usize>, Arc<Self>>) -> Arc<Self> {
        if self.children.is_empty()
            && let Some(recorder) = recorders.get(&self.path)
        {
            return recorder.clone();
        }
        let result = Arc::new(Self {
            site: self.site.clone(),
            path: self.path.clone(),
            state: std::sync::Mutex::new(self.state().clone()),
            children: self
                .children
                .iter()
                .map(|(key, child)| (key.clone(), child.fork_loop_entry(recorders)))
                .collect(),
        });
        if self.children.is_empty() {
            recorders.insert(self.path.clone(), result.clone());
        }
        result
    }

    fn merge_loop_entries(&self, paths: &[&Self], branches: &LoopEntryBranches) {
        if self.result().is_none() {
            let result = guarded_entry_expansion(
                branches,
                &paths
                    .iter()
                    .map(|capture| capture.result())
                    .collect::<Vec<_>>(),
            );
            self.state().result = result;
        }
        for (key, child) in &self.children {
            let children = paths
                .iter()
                .map(|capture| capture.children.get(key).expect("forked child").as_ref())
                .collect::<Vec<_>>();
            child.merge_loop_entries(&children, branches);
        }
    }

    fn new(site: ProofSite, path: Vec<usize>) -> Self {
        Self {
            site,
            path,
            state: std::sync::Mutex::new(NestedTacticCaptureState::default()),
            children: BTreeMap::new(),
        }
    }

    fn collection(site: ProofSite, children: BTreeMap<Vec<usize>, Arc<Self>>) -> Self {
        Self {
            site,
            path: Vec::new(),
            state: std::sync::Mutex::default(),
            children,
        }
    }

    pub(in crate::surface) fn at_path(self: &Arc<Self>, path: &[usize]) -> Option<Arc<Self>> {
        if self.path == path {
            Some(self.clone())
        } else {
            self.children.get(path).cloned()
        }
    }

    fn state(&self) -> std::sync::MutexGuard<'_, NestedTacticCaptureState> {
        self.state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Claims the recorder for one occurrence of the selected tactic.
    pub(in crate::surface) fn try_begin(&self) -> bool {
        let mut state = self.state();
        if state.active {
            return false;
        }
        state.active = true;
        true
    }

    /// Records one checked occurrence. Every occurrence (one per C path or
    /// outcome that checks the body) must expand identically; the first
    /// disagreement is the answer.
    pub(in crate::surface) fn finish(&self, occurrence: Result<Vec<ProofTactic>, String>) {
        let mut state = self.state();
        state.active = false;
        match (&state.result, occurrence) {
            (None, occurrence) => state.result = Some(occurrence),
            (Some(Ok(existing)), Ok(tactics)) if *existing == tactics => {}
            (Some(Ok(_)), Ok(_)) => {
                state.result = Some(Err(
                    "selected tactic expands differently across proof obligations".to_string(),
                ));
            }
            (Some(Ok(_)), Err(error)) => state.result = Some(Err(error)),
            (Some(Err(_)), _) => {}
        }
    }

    /// Releases the recorder after an occurrence that did not complete.
    pub(in crate::surface) fn abandon(&self) {
        self.state().active = false;
    }

    pub(in crate::surface) fn result(&self) -> Option<Result<Vec<ProofTactic>, String>> {
        self.state().result.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum ProofSite {
    FunctionClaim {
        function_name: String,
        claim: ContractProofClaim,
    },
    TheoremEnsure {
        theorem_name: String,
        ensure_index: usize,
    },
}

impl ProofSite {
    pub(super) fn description(&self) -> String {
        match self {
            Self::FunctionClaim {
                function_name,
                claim,
            } => format!("function `{function_name}` {}", claim.describe()),
            Self::TheoremEnsure {
                theorem_name,
                ensure_index,
            } => format!("theorem `{theorem_name}` ensure {ensure_index}"),
        }
    }
}

#[derive(Clone, Debug)]
enum TacticSourceEdit {
    Partial(Range<usize>),
    /// The implicit tail of a written script, written in after the script's
    /// last written tactic, which ends at this offset.
    Append(usize),
    PartialProofClause(Range<usize>),
    WholeProof(ProofSourceEdit),
}

#[derive(Clone, Debug)]
struct LocatedSourceTactic {
    site: ProofSite,
    /// The claim-level source index: the selected tactic's own, or that of
    /// the outermost `have` whose body contains it.
    source_index: usize,
    /// The rest of the source path, outermost first: the written position
    /// inside each nested `have` body, or the arm and then the written
    /// position inside each `if` or `cases` arm; empty for a claim-level
    /// tactic.
    nested: Vec<usize>,
    edit: TacticSourceEdit,
    /// Where each claim-level tactic of this site starts in the source, by
    /// source index: an expansion that stands for a run of tactics ending at
    /// the selected one replaces from an earlier one of these.
    sibling_starts: Vec<(usize, usize)>,
    /// The function block the selected site belongs to, for printing its
    /// parameters' places. Filled for the one tactic an expansion selects.
    function_block: Option<FunctionBlock>,
    /// Where the parse of the selecting file read its proofs, so an edit
    /// can address the implicit block of a one-tactic proof.
    source_spans: Arc<parser::SourceSpans>,
}

thread_local! {
    /// The claim-level source index an expansion replaces from, when the
    /// recorded tactics stand for more than the selected tactic.
    static EXPANSION_REPLACES_FROM: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// Records that the expansion captured for the selected tactic also stands
/// for the tactics written before it, back to `source_index`. A closer of a
/// loop phase shared by several invariants expands to one step per
/// invariant, each holding the whole shared script; the written tactics
/// before the closer are part of what it replaces.
pub(in crate::surface) fn note_expansion_replaces_from(source_index: usize) {
    EXPANSION_REPLACES_FROM.with(|from| from.set(Some(source_index)));
}

pub(in crate::surface) fn take_expansion_replaces_from() -> Option<usize> {
    EXPANSION_REPLACES_FROM.with(std::cell::Cell::take)
}

/// A selected rewrite and the emitted regions in its Click source. Audit
/// uses these regions to check its fixed point without expanding unselected
/// automation between them.
#[derive(Clone, Debug)]
pub struct SelectedTacticExpansion {
    pub source: String,
    pub replacement_spans: Vec<Range<usize>>,
}

impl SelectedTacticExpansion {
    fn whole_rewrite(original: &str, source: String) -> Self {
        let prefix = original
            .chars()
            .zip(source.chars())
            .take_while(|(a, b)| a == b)
            .map(|(c, _)| c.len_utf8())
            .sum::<usize>();
        let suffix = original[prefix..]
            .chars()
            .rev()
            .zip(source[prefix..].chars().rev())
            .take_while(|(a, b)| a == b)
            .map(|(c, _)| c.len_utf8())
            .sum::<usize>();
        let replacement_spans = std::iter::once(prefix..source.len() - suffix).collect();
        Self {
            source,
            replacement_spans,
        }
    }
}

/// Expands just the requested sites of one claim in a shared verification.
pub fn expand_c_tactics_source_at(
    source: &str,
    c_sources: &[(&str, &str)],
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    expand_selected_tactics_context(
        None,
        source,
        &ProgramSourceContext::bundle(c_sources),
        positions,
    )
}

pub fn expand_project_tactics_source_at(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    let source = project
        .entry_source()
        .ok_or_else(|| ClickError::new("missing entry source"))?;
    expand_selected_tactics_context(
        Some(project),
        source,
        &ProgramSourceContext::of(inputs)?.with_click_project(project),
        positions,
    )
}

pub fn expand_tactics_source_at(
    source: &str,
    inputs: &ProgramInputs<'_>,
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    expand_selected_tactics_context(None, source, &ProgramSourceContext::of(inputs)?, positions)
}

fn expand_selected_tactics_context(
    project: Option<&ClickProject>,
    source: &str,
    inputs: &ProgramSourceContext<'_>,
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    if positions.is_empty() {
        return Ok(SelectedTacticExpansion {
            source: source.to_string(),
            replacement_spans: Vec::new(),
        });
    }
    let file = match project {
        Some(project) => resolve_click_project_context(project, inputs)?,
        None => parse_source_with_program_layouts_context(source, inputs)?,
    };
    let _binder_names = printing::CertificateBinderScope::enter(source, file.function_blocks());
    let wanted = positions
        .iter()
        .map(|p| (p.line, p.column))
        .collect::<BTreeSet<_>>();
    let mut offsets = BTreeSet::new();
    let (mut line, mut column) = (1, 1);
    for (offset, character) in source.char_indices() {
        crate::instrumentation::record_deterministic_work(1);
        if offset % 1024 == 0 && crate::instrumentation::deadline_exceeded() {
            return Err(ClickError::new(
                "selected expansion exceeded its time limit",
            ));
        }
        if wanted.contains(&(line, column)) {
            offsets.insert(offset);
        }
        if character == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    let entries = source_tactic_entries(source, &file)?;
    let mut selected = BTreeMap::<usize, LocatedSourceTactic>::new();
    for entry in &entries {
        if !offsets.contains(&entry.anchor) {
            continue;
        }
        if let EntrySelection::Located(located) = &entry.selection {
            selected
                .entry(entry.anchor)
                .or_insert_with(|| located.clone());
        }
    }
    if selected.len() != wanted.len() {
        return Err(ClickError::new(
            "selected audit locations no longer name proof tactics",
        ));
    }
    let selected = selected.into_values().collect::<Vec<_>>();
    let site = selected[0].site.clone();
    if selected.iter().any(|target| target.site != site) {
        return Err(ClickError::new(
            "batch expansion requires sites from one claim",
        ));
    }
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &site
    {
        let verified = match project {
            Some(project) => verify_click_project_theorem_context(project, inputs, theorem_name)?,
            None => verify_click_theorem_context(source, inputs, theorem_name)?,
        };
        return rewrite_verified_pure_theorem(source, &verified, theorem_name, *ensure_index)
            .map(|rewritten| SelectedTacticExpansion::whole_rewrite(source, rewritten));
    }
    let contract_value_parameters = contract_value_parameter_names(file.contract_definitions());
    let site_signature = match &site {
        ProofSite::FunctionClaim { function_name, .. } => proof_function_blocks(&file)
            .find(|block| block.signature().name() == function_name)
            .map(|block| block.signature().clone()),
        ProofSite::TheoremEnsure { .. } => None,
    };
    let reference_result = site_signature
        .as_ref()
        .is_some_and(FunctionSignature::returns_reference);
    let _reference_result_source =
        super::diagnostics::ReferenceResultSourceScope::enter(reference_result);
    let whole = selected
        .iter()
        .any(|target| matches!(target.edit, TacticSourceEdit::WholeProof(_)));
    let targets = selected
        .iter()
        .map(|t| (t.source_index, t.nested.clone()))
        .collect::<Vec<_>>();
    let mut capture = if whole {
        ExpansionCapture::for_site(site.clone())
    } else {
        ExpansionCapture::for_tactics(site.clone(), &targets)
    };
    take_expansion_replaces_from();
    let whole_function = match &site {
        ProofSite::FunctionClaim {
            function_name,
            claim,
        } if whole => Some((function_name, *claim)),
        _ => None,
    };
    let (verified, _) = instrumentation::with_default_tactic_limits(|| {
        crate::surface::verification::verify_program_with_context(
            source,
            inputs,
            whole_function.map(|(name, _)| VerificationTarget::Function(name.clone())),
            None,
            if whole_function.is_some() {
                None
            } else {
                Some(&mut capture)
            },
            Some(file),
        )
    })?;
    // The whole claim's tactics are rendered below, after checking ended:
    // spell their step results by the checked function's layout.
    let mut _whole_claim_spelling = None;
    if let Some((name, claim)) = whole_function {
        let theorem = select_expansion_theorem(&verified, name, claim)?;
        _whole_claim_spelling = theorem.step_result_spelling_scope();
        let mut tactics = theorem.expanded_proof_certificate()?.to_proof_tactics();
        if theorem.function_block.is_tactic_procedure() {
            remove_tactic_procedure_ending(
                &mut tactics,
                super::verification::tactic_procedure_ending_len(&theorem.function_block),
            )
            .map_err(|()| ClickError::new("expanded tactic procedure lost its checked ending"))?;
        } else {
            tactics = sequential_early_returns(tactics, theorem.checked_execution.function());
        }
        capture.result = Some(Ok(tactics));
    }
    let sibling_starts = entries
        .iter()
        .filter_map(|entry| match &entry.selection {
            EntrySelection::Located(sibling)
                if sibling.site == site && sibling.nested.is_empty() =>
            {
                Some((sibling.source_index, entry.span.start))
            }
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let edit_span = |target: &LocatedSourceTactic| {
        let mut span = match &target.edit {
            TacticSourceEdit::Partial(span) | TacticSourceEdit::PartialProofClause(span) => {
                span.clone()
            }
            TacticSourceEdit::Append(at) => *at..*at,
            TacticSourceEdit::WholeProof(edit) => edit.span().clone(),
        };
        if let Some(from) = capture
            .batch
            .as_ref()
            .and_then(|batch| batch.targets.get(&target.source_index))
            .and_then(|recorder| recorder.replaces_from)
            .and_then(|index| sibling_starts.get(&index))
        {
            span.start = span.start.min(*from);
        }
        span
    };
    let mut selected = selected;
    selected.sort_by_key(|target| {
        let span = edit_span(target);
        (span.start, std::cmp::Reverse(span.end))
    });
    // The certificate is printed as the claim's own function spells its
    // places, whichever function the verification checked last.
    super::diagnostics::enter_rust_spelling(site_signature.as_ref());
    let _contract_value_parameters = contract_value_parameters
        .as_ref()
        .map(printing::ContractValueParameterScope::enter);
    let mut edits: Vec<(Range<usize>, String)> = Vec::new();
    for target in selected {
        let owned_span = edit_span(&target);
        if edits
            .last()
            .is_some_and(|(span, _)| owned_span.start >= span.start && owned_span.end <= span.end)
        {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        let recorder = capture
            .batch
            .as_ref()
            .and_then(|batch| batch.targets.get(&target.source_index))
            .unwrap_or(&capture);
        let result = if target.nested.is_empty() {
            recorder.result.clone()
        } else {
            let mut path = vec![target.source_index];
            path.extend(&target.nested);
            recorder
                .nested
                .as_ref()
                .and_then(|nested| nested.at_path(&path))
                .and_then(|nested| nested.result())
        };
        let tactics = match result {
            Some(result) => result.map_err(ClickError::new)?,
            None if recorder.dropped_path_occurrence => Vec::new(),
            None => {
                return Err(ClickError::new(format!(
                    "selected {} tactic {} retained no expansion",
                    site.description(),
                    target.source_index
                )));
            }
        };
        let (mut span, replacement) = match target.edit {
            TacticSourceEdit::Partial(span) => (
                span,
                super::printing::format_partial_tactic_sequence(&tactics),
            ),
            TacticSourceEdit::Append(at) => (at..at, appended_tail(&tactics)),
            TacticSourceEdit::PartialProofClause(span) if tactics.is_empty() => {
                (span, format!("by {{ {} }}", printing::CLOSE_CALL))
            }
            TacticSourceEdit::PartialProofClause(span) => (
                span,
                super::printing::format_proof_certificate(
                    &ProofCertificate::from_proof_tactics(&tactics)
                        .map_err(|error| ClickError::new(error.message().to_string()))?,
                ),
            ),
            TacticSourceEdit::WholeProof(edit) => {
                let replacement = super::printing::format_proof_certificate(
                    &ProofCertificate::from_proof_tactics(&tactics)
                        .map_err(|error| ClickError::new(error.message().to_string()))?,
                );
                let span = edit.span().clone();
                let replacement = match edit {
                    ProofSourceEdit::Explicit(_) => replacement,
                    ProofSourceEdit::DefaultTerminator { .. } => format!(" {replacement}"),
                    ProofSourceEdit::OmittedLoopPhase { phase, .. } => {
                        format!("    {phase} {}\n", replacement.replace('\n', "\n    "))
                    }
                };
                (span, replacement)
            }
        };
        if let Some(from) = recorder
            .replaces_from
            .and_then(|index| sibling_starts.get(&index))
        {
            span.start = span.start.min(*from);
        }
        let replacement = if replacement.is_empty()
            && source[..span.start].trim_end().ends_with('{')
            && source[span.end..].trim_start().starts_with('}')
        {
            printing::CLOSE_CALL.to_string()
        } else {
            replacement
        };
        edits.push((
            span.clone(),
            indent_replacement(source, span.start, &replacement),
        ));
    }
    // A prefix expansion owns any selected edits within that prefix. Reject
    // crossing ranges rather than constructing an ambiguous rewrite.
    edits.sort_by_key(|(span, _)| (span.start, std::cmp::Reverse(span.end)));
    let mut retained: Vec<(Range<usize>, String)> = Vec::new();
    for (span, replacement) in edits {
        if let Some((previous, _)) = retained.last() {
            if span.end <= previous.end {
                continue;
            }
            if span.start < previous.end {
                return Err(ClickError::new(
                    "selected expansion edits overlap without one owning the other",
                ));
            }
        }
        retained.push((span, replacement));
    }
    let mut rewritten = String::with_capacity(source.len());
    let mut cursor = 0;
    let mut replacement_spans = Vec::new();
    for (span, replacement) in retained {
        let replacement = require_surface_expansion(replacement)?;
        rewritten.push_str(&source[cursor..span.start]);
        let replacement_start = rewritten.len();
        rewritten.push_str(&replacement);
        replacement_spans.push(replacement_start..rewritten.len());
        cursor = span.end;
    }
    rewritten.push_str(&source[cursor..]);
    // Removing several no-op occurrences can empty a proof block together.
    // Fill only blocks touched by this rewrite, preserving unrelated syntax.
    let tokens = plain_source_tokens(&rewritten)?;
    let mut region = 0;
    let mut empty_blocks = Vec::new();
    for window in tokens.windows(3) {
        while replacement_spans
            .get(region)
            .is_some_and(|span| span.end < window[1].span.end)
        {
            region += 1;
        }
        if window[0].text == "by"
            && window[1].text == "{"
            && window[2].text == "}"
            && replacement_spans.get(region).is_some_and(|span| {
                span.start <= window[2].span.start && span.end >= window[1].span.end
            })
        {
            empty_blocks.push(window[1].span.end);
        }
    }
    for offset in empty_blocks.into_iter().rev() {
        let filler = format!(" {} ", printing::CLOSE_CALL);
        rewritten.insert_str(offset, &filler);
        for span in &mut replacement_spans {
            if span.start >= offset {
                span.start += filler.len();
            }
            if span.end >= offset {
                span.end += filler.len();
            }
        }
    }
    if let Some(project) = project {
        let rewritten_project = project.with_entry_source(rewritten.clone());
        resolve_click_project_context(&rewritten_project, inputs)?;
    } else {
        parse_source_with_program_layouts_context(&rewritten, inputs)?;
    }
    Ok(SelectedTacticExpansion {
        source: rewritten,
        replacement_spans,
    })
}

impl LocatedSourceTactic {
    /// The span this tactic's expansion replaces and its rendered
    /// replacement text.
    fn replacement(
        &self,
        click_source: &str,
        file: &ClickFile,
        replacement_tactics: &[ProofTactic],
    ) -> Result<(Range<usize>, String), ClickError> {
        let _binder_names =
            printing::CertificateBinderScope::enter(click_source, file.function_blocks());
        let _contract_value_parameters = printing::ContractValueParameterScope::for_file(file);
        let certificate = || {
            ProofCertificate::from_proof_tactics(replacement_tactics)
                .map(|certificate| super::printing::format_proof_certificate(&certificate))
                .map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: its expansion still contains {}",
                        error.message()
                    ))
                })
        };
        Ok(match self.edit.clone() {
            TacticSourceEdit::Partial(span) => (
                self.replaced_span(span),
                super::printing::format_partial_tactic_sequence(replacement_tactics),
            ),
            TacticSourceEdit::Append(at) => (at..at, appended_tail(replacement_tactics)),
            // A whole phase can contribute no steps, but its written block
            // must still contain a checked tactic.
            TacticSourceEdit::PartialProofClause(span) if replacement_tactics.is_empty() => {
                (span, format!("by {{ {} }}", printing::CLOSE_CALL))
            }
            TacticSourceEdit::PartialProofClause(span) => (span, certificate()?),
            TacticSourceEdit::WholeProof(edit) => {
                let replacement = certificate()?;
                let span = edit.span().clone();
                let replacement = match edit {
                    ProofSourceEdit::Explicit(_) => replacement,
                    ProofSourceEdit::DefaultTerminator { .. } => {
                        let separator = click_source[..span.start]
                            .chars()
                            .next_back()
                            .is_some_and(|character| !character.is_whitespace());
                        format!("{}{replacement}", if separator { " " } else { "" })
                    }
                    ProofSourceEdit::OmittedLoopPhase { phase, .. } => {
                        format!("    {phase} {}\n", replacement.replace('\n', "\n    "))
                    }
                };
                (span, replacement)
            }
        })
    }

    /// `span` widened back to the tactic a recorded
    /// [`note_expansion_replaces_from`] names, if any.
    fn replaced_span(&self, span: Range<usize>) -> Range<usize> {
        let Some(from) = EXPANSION_REPLACES_FROM.with(std::cell::Cell::take) else {
            return span;
        };
        self.sibling_starts
            .iter()
            .find(|(source_index, start)| *source_index == from && *start < span.start)
            .map_or(span.clone(), |(_, start)| *start..span.end)
    }
}

/// One written tactic in the span-indexed side table that source selection
/// consults. Every tactic at every depth is recorded by its source span; the
/// flat claim-level numbering stays exactly the one timing, profiling, and
/// audit use, and a tactic inside a `have` body is addressed by that `have`'s
/// number plus its written positions.
#[derive(Clone, Debug)]
struct SourceTacticEntry {
    span: Range<usize>,
    /// The canonical start the tactic is reported at.
    anchor: usize,
    claim_label: String,
    tactic_name: String,
    smart: bool,
    /// A simple written operation whose implicit obligation proofs can be
    /// extracted when a user explicitly selects its location.
    has_implicit_obligations: bool,
    selection: EntrySelection,
}

#[derive(Clone, Debug)]
enum EntrySelection {
    Located(LocatedSourceTactic),
    /// A smart tactic the expander cannot address separately, and why.
    Unaddressable(String),
}

/// One smart tactic that a source location can select.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmartTacticCandidate {
    pub claim_label: String,
    pub tactic_name: String,
    /// Where the tactic starts, in the Click source's own coordinates.
    pub position: SourcePosition,
}

/// Why a source location selects no single smart tactic. `candidates` lists
/// the smart tactics the location could have meant, if any.
#[derive(Clone, Debug)]
pub struct SmartTacticSelectionError {
    pub reason: String,
    pub candidates: Vec<SmartTacticCandidate>,
}

impl SmartTacticSelectionError {
    fn from_error(error: ClickError) -> Self {
        Self {
            reason: error.message().to_string(),
            candidates: Vec::new(),
        }
    }

    /// The error in Click source coordinates, for callers without a
    /// container file to report positions in.
    fn into_click_error(self, line: usize, column: Option<usize>) -> ClickError {
        let location =
            column.map_or_else(|| format!("{line}"), |column| format!("{line}:{column}"));
        let mut message = format!("source location {location}: {}", self.reason);
        for candidate in &self.candidates {
            message.push_str(&format!(
                "\n  {}:{} `{}` in `{}`",
                candidate.position.line,
                candidate.position.column,
                candidate.tactic_name,
                candidate.claim_label
            ));
        }
        ClickError::new(message)
    }
}

/// Resolves a source location to one tactic with expandable proof work.
///
/// With a column, the location selects the innermost eligible tactic whose
/// source span contains it. Without one, the line must start exactly one
/// eligible tactic. The result's position is the tactic's canonical start.
pub fn c_select_smart_tactic(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    select_smart_tactic(
        click_source,
        &ProgramInputs::Bundle(c_sources.to_vec()),
        line,
        column,
    )
}

pub fn select_smart_tactic(
    click_source: &str,
    inputs: &ProgramInputs<'_>,
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let sources =
        ProgramSourceContext::of(inputs).map_err(SmartTacticSelectionError::from_error)?;
    let file = parse_source_with_program_layouts_context(click_source, &sources)
        .map_err(SmartTacticSelectionError::from_error)?;
    select_smart_tactic_file(click_source, &file, line, column)
}

pub fn project_select_smart_tactic(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let sources = ProgramSourceContext::of(inputs)
        .map_err(SmartTacticSelectionError::from_error)?
        .with_click_project(project);
    let click_source = project.entry_source().ok_or_else(|| {
        SmartTacticSelectionError::from_error(ClickError::new(format!(
            "missing entry module `{}`",
            project.entry()
        )))
    })?;
    let file = resolve_click_project_context(project, &sources)
        .map_err(SmartTacticSelectionError::from_error)?;
    select_smart_tactic_file(click_source, &file, line, column)
}

fn select_smart_tactic_file(
    click_source: &str,
    file: &ClickFile,
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let entries =
        source_tactic_entries(click_source, file).map_err(SmartTacticSelectionError::from_error)?;
    let entry = select_source_tactic_entry(click_source, &entries, line, column)?;
    Ok(smart_tactic_candidate(click_source, entry))
}

/// One claim a source location can name: the label `click expand --claim`
/// and `click audit --claim` take, the function or theorem that owns it
/// (the proof unit `click verify --trace-proof` traces), and where its
/// clause or proof starts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceClaim {
    pub label: String,
    pub owner: String,
    /// Where the claim's clause, or its proof when that is all the claim
    /// writes, starts, in the Click source's own coordinates.
    pub position: SourcePosition,
}

/// Why a source location names no single claim. `candidates` lists the
/// claims the location could have meant, if any.
#[derive(Clone, Debug)]
pub struct ClaimLocationError {
    pub reason: String,
    pub candidates: Vec<SourceClaim>,
}

impl ClaimLocationError {
    fn from_error(error: ClickError) -> Self {
        Self {
            reason: error.message().to_string(),
            candidates: Vec::new(),
        }
    }
}

/// How finely a source location names a claim.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClaimLocationScope {
    /// The innermost claim, including a loop phase proved by a `loop`
    /// tactic inside a claim's proof script, `f.loop(N).maintain`. The
    /// source does not say which C loop such a tactic proves, so naming its
    /// phase checks the proof that writes it.
    Innermost,
    /// The claim whose proof is checked as one unit: a loop phase inside a
    /// proof script names that proof, and nothing is verified.
    ProofUnit,
}

/// The claim whose clause or proof covers a source location of a sidecar
/// (or, with `project`, of its entry module).
///
/// A claim covers the source from its clause's keyword through the end of
/// its proof: an `ensures`, `owns`, or `produces` clause and its `by`, an
/// `exceptional ensures` clause, a loop phase proof, a function's grouped
/// proof, or a tactic's proof. A clause without its own proof that the
/// grouped proof covers names the grouped proof, `f.contract`, which is the
/// claim that proves it. With [`ClaimLocationScope::Innermost`], a written
/// `initialize` or `maintain` proof of a `loop` tactic in a proof script is
/// a claim inside the claim whose proof writes it. With a column the
/// location selects the innermost claim containing it; without one, the
/// line must touch exactly one claim that contains no other claim touching
/// it.
pub fn claim_at(
    project: Option<&ClickProject>,
    click_source: &str,
    inputs: &ProgramInputs<'_>,
    line: usize,
    column: Option<usize>,
    scope: ClaimLocationScope,
) -> Result<SourceClaim, ClaimLocationError> {
    let sources = ProgramSourceContext::of(inputs).map_err(ClaimLocationError::from_error)?;
    let (click_source, sources, file) = match project {
        Some(project) => {
            let sources = sources.with_click_project(project);
            let click_source = project.entry_source().ok_or_else(|| {
                ClaimLocationError::from_error(ClickError::new(format!(
                    "missing entry module `{}`",
                    project.entry()
                )))
            })?;
            let file = resolve_click_project_context(project, &sources)
                .map_err(ClaimLocationError::from_error)?;
            (click_source, sources, file)
        }
        None => {
            let file = parse_source_with_program_layouts_context(click_source, &sources)
                .map_err(ClaimLocationError::from_error)?;
            (click_source, sources, file)
        }
    };
    let regions =
        claim_source_regions(click_source, &file, scope).map_err(ClaimLocationError::from_error)?;
    let region = select_claim_region(click_source, &regions, line, column)?;
    let label = match &region.written_phase {
        None => region.label.clone(),
        Some((tactic, phase)) => {
            let bound =
                bind_written_loop_tactics(click_source, &sources, &file, std::slice::from_ref(tactic))
                    .remove(0)
                    .map_err(|error| ClaimLocationError {
                        reason: format!(
                            "{} names a loop phase, but which C loop its `loop` tactic proves could not be determined: {}",
                            region.label,
                            error.message()
                        ),
                        candidates: Vec::new(),
                    })?;
            let CodeRegion::Loop(loop_index) = bound.region() else {
                return Err(ClaimLocationError::from_error(ClickError::new(
                    "a checked `loop` tactic was bound to no loop",
                )));
            };
            claim_labels::loop_phase_claim_label(&region.owner, *loop_index, phase)
        }
    };
    Ok(SourceClaim {
        label,
        owner: region.owner.clone(),
        position: position_at_offset(click_source, region.anchor),
    })
}

/// One claim and the source it covers.
struct ClaimRegion {
    span: Range<usize>,
    /// Where the claim is reported: its clause's start, or its proof's.
    anchor: usize,
    /// The claim's label; for a written phase of a `loop` tactic, which
    /// checked execution binds, a description of it until it is bound.
    label: String,
    owner: String,
    /// The `loop` tactic and phase a written loop phase proof in a proof
    /// script belongs to.
    written_phase: Option<(WrittenLoopTactic, &'static str)>,
}

/// Every claim of the source's selected theorems, functions, and tactics,
/// with the source each covers. A claim whose source cannot be located is
/// left out: it cannot be selected by location.
fn claim_source_regions(
    click_source: &str,
    file: &ClickFile,
    scope: ClaimLocationScope,
) -> Result<Vec<ClaimRegion>, ClickError> {
    let source_tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let tokens = ProofTokens::new(file, &source_tokens);
    let declarations = DeclarationSources::new(&tokens);
    let mut regions = Vec::new();
    let clause_region = |clause: usize, edit: &ProofSourceEdit| {
        let start = tokens[clause].span.start;
        start..edit.span().end.max(start)
    };
    if let Some((start, end)) = &file.termination_span {
        let first = declarations
            .token_at(start, Some("termination"))
            .expect("parser recorded termination keyword");
        let last = declarations
            .token_at(end, Some("}"))
            .expect("parser recorded termination block");
        let span = tokens[first].span.start..tokens[last].span.end;
        regions.push(ClaimRegion {
            anchor: span.start,
            span,
            label: "program.termination".into(),
            owner: "program.termination".into(),
            written_phase: None,
        });
    }
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        let Ok(source) = declarations.theorem(theorem) else {
            continue;
        };
        for index in 0..theorem.ensures().len() {
            let Ok((clause, proof)) = written_clause(&source, index) else {
                continue;
            };
            let span = clause_region(clause, &claim_proof_edit(&tokens, clause, proof));
            regions.push(ClaimRegion {
                anchor: span.start,
                span,
                label: theorem.ensure_claim_label(index),
                owner: theorem.name().to_string(),
                written_phase: None,
            });
        }
    }
    for function_block in proof_function_blocks(file) {
        if function_block.is_external() {
            continue;
        }
        let function_name = function_block.signature().name();
        let Ok(function) = declarations.function(function_block) else {
            continue;
        };
        let owner = function_name.to_string();
        if function_block.grouped_proof().is_some()
            && let Ok(span) = find_grouped_proof_span(&tokens, &function)
        {
            regions.push(ClaimRegion {
                anchor: span.start,
                span,
                label: function_block.contract_claim_label(),
                owner: owner.clone(),
                written_phase: None,
            });
        }
        // A claim the grouped proof covers is proved there, so its clause
        // names that proof.
        let label = |claim: ContractProofClaim| {
            function_block.claim_label(covering_claim(function_block, claim))
        };
        let mut written = None;
        for index in 0..function_block.ensures().len() {
            // The members of a flattened aggregate clause share their
            // written clause, its label, and its proof.
            let source = function_block.ensure_source_clause(index);
            if written.replace(source) == Some(source) {
                continue;
            }
            let Ok((clause, proof)) = written_clause(&function, source) else {
                continue;
            };
            let span = clause_region(clause, &claim_proof_edit(&tokens, clause, proof));
            regions.push(ClaimRegion {
                anchor: span.start,
                span,
                label: label(ContractProofClaim::Ensure(index)),
                owner: owner.clone(),
                written_phase: None,
            });
        }
        for index in 0..function_block.exceptional_ensures().len() {
            let Ok((clause, proof)) = written_exceptional_clause(&function, index) else {
                continue;
            };
            let span = clause_region(clause, &claim_proof_edit(&tokens, clause + 1, proof));
            regions.push(ClaimRegion {
                anchor: span.start,
                span,
                label: label(ContractProofClaim::ExceptionalEnsure(index)),
                owner: owner.clone(),
                written_phase: None,
            });
        }
    }
    if scope == ClaimLocationScope::Innermost {
        for tactic in written_loop_tactics(click_source, &tokens, file)? {
            for phase in ["initialize", "maintain", "otherwise"] {
                let (Some(keyword), edit) = written_loop_phase(&tokens, &tactic, phase)? else {
                    continue;
                };
                regions.push(ClaimRegion {
                    anchor: keyword,
                    span: keyword..edit.span().end,
                    label: format!(
                        "the `{phase}` proof of the `loop` tactic in `{}`",
                        tactic.claim_label
                    ),
                    owner: tactic.function_name.clone(),
                    written_phase: Some((tactic.clone(), phase)),
                });
            }
        }
    }
    Ok(regions)
}

/// The one claim a location selects among `regions`: with a column, the
/// innermost claim containing it; without one, the only claim (by label)
/// whose source touches the line.
fn select_claim_region<'r>(
    click_source: &str,
    regions: &'r [ClaimRegion],
    line: usize,
    column: Option<usize>,
) -> Result<&'r ClaimRegion, ClaimLocationError> {
    let claim = |region: &ClaimRegion| SourceClaim {
        label: region.label.clone(),
        owner: region.owner.clone(),
        position: position_at_offset(click_source, region.anchor),
    };
    let line_start =
        offset_at_position(click_source, line, 1).map_err(ClaimLocationError::from_error)?;
    let line_end = click_source[line_start..]
        .find('\n')
        .map_or(click_source.len(), |newline| line_start + newline);
    let on_line = || {
        let all_touching = regions
            .iter()
            .filter(|region| region.span.start <= line_end && region.span.end > line_start)
            .collect::<Vec<_>>();
        let mut touching: Vec<&ClaimRegion> = Vec::new();
        for &region in &all_touching {
            // A claim written inside another names the line it touches; the
            // claim around it does not.
            let encloses_another = all_touching.iter().any(|inner| {
                inner.span != region.span
                    && region.span.start <= inner.span.start
                    && inner.span.end <= region.span.end
            });
            if !encloses_another && touching.iter().all(|seen| seen.label != region.label) {
                touching.push(region);
            }
        }
        touching
    };
    match column {
        Some(column) => {
            let wanted = offset_at_position(click_source, line, column)
                .map_err(ClaimLocationError::from_error)?;
            // Claims nest only where a proof script writes a loop phase;
            // the shorter is the more specific.
            if let Some(region) = regions
                .iter()
                .filter(|region| region.span.contains(&wanted))
                .min_by_key(|region| region.span.end - region.span.start)
            {
                return Ok(region);
            }
            let touching = on_line();
            Err(ClaimLocationError {
                reason: if touching.is_empty() {
                    "no claim's clause or proof contains this location".to_string()
                } else {
                    "no claim's clause or proof contains this location; the claims on this line are:"
                        .to_string()
                },
                candidates: touching.into_iter().map(claim).collect(),
            })
        }
        None => match on_line().as_slice() {
            [] => Err(ClaimLocationError {
                reason: "no claim's clause or proof covers this line".to_string(),
                candidates: Vec::new(),
            }),
            [only] => Ok(only),
            several => Err(ClaimLocationError {
                reason: format!(
                    "{} claims cover this line; add the column of one of them:",
                    several.len()
                ),
                candidates: several.iter().map(|region| claim(region)).collect(),
            }),
        },
    }
}

fn smart_tactic_candidate(click_source: &str, entry: &SourceTacticEntry) -> SmartTacticCandidate {
    SmartTacticCandidate {
        claim_label: entry.claim_label.clone(),
        tactic_name: entry.tactic_name.clone(),
        position: position_at_offset(click_source, entry.anchor),
    }
}

/// Select an expandable entry by its span or the start of its line.
fn select_source_tactic_entry<'e>(
    click_source: &str,
    entries: &'e [SourceTacticEntry],
    line: usize,
    column: Option<usize>,
) -> Result<&'e SourceTacticEntry, SmartTacticSelectionError> {
    // A smart tactic written inside a smart site that owns it (the `solve`
    // of a smart `have`) is an alias of that site; the line lists the site
    // once.
    let selectable = |entry: &SourceTacticEntry| entry.smart || entry.has_implicit_obligations;
    let starting_on_line = || {
        let mut starting: Vec<&SourceTacticEntry> = Vec::new();
        for entry in entries.iter().filter(|entry| {
            selectable(entry) && position_at_offset(click_source, entry.anchor).line == line
        }) {
            if !starting
                .iter()
                .any(|seen| same_selection(&seen.selection, &entry.selection))
            {
                starting.push(entry);
            }
        }
        starting
    };
    let innermost_containing = |wanted: usize| {
        // Spans nest, so the shortest containing span is the innermost;
        // equal spans keep source order.
        entries
            .iter()
            .filter(|entry| {
                selectable(entry) && (entry.span.contains(&wanted) || entry.anchor == wanted)
            })
            .min_by_key(|entry| entry.span.end - entry.span.start)
    };
    let candidates = |entries: &[&SourceTacticEntry]| {
        entries
            .iter()
            .map(|entry| smart_tactic_candidate(click_source, entry))
            .collect::<Vec<_>>()
    };
    let selected = match column {
        Some(column) => {
            let wanted = offset_at_position(click_source, line, column)
                .map_err(SmartTacticSelectionError::from_error)?;
            match innermost_containing(wanted) {
                Some(entry) => entry,
                None => {
                    let on_line = starting_on_line();
                    return Err(SmartTacticSelectionError {
                        reason: if on_line.is_empty() {
                            "no smart tactic's source contains this location".to_string()
                        } else {
                            "no smart tactic's source contains this location; the smart tactics starting on this line are:".to_string()
                        },
                        candidates: candidates(&on_line),
                    });
                }
            }
        }
        None => match starting_on_line().as_slice() {
            [] => {
                // A line inside a region the expander cannot address says
                // why, as a column there would.
                let line_start = offset_at_position(click_source, line, 1)
                    .map_err(SmartTacticSelectionError::from_error)?;
                let indent = click_source[line_start..]
                    .find(|character: char| !character.is_whitespace() || character == '\n')
                    .unwrap_or(0);
                if let Some(SourceTacticEntry {
                    selection: EntrySelection::Unaddressable(reason),
                    ..
                }) = innermost_containing(line_start + indent)
                {
                    return Err(SmartTacticSelectionError {
                        reason: reason.clone(),
                        candidates: Vec::new(),
                    });
                }
                return Err(SmartTacticSelectionError {
                    reason: "no smart tactic starts on this line".to_string(),
                    candidates: Vec::new(),
                });
            }
            [only] => only,
            several => {
                return Err(SmartTacticSelectionError {
                    reason: format!(
                        "{} smart tactics start on this line; add the column of one of them:",
                        several.len()
                    ),
                    candidates: candidates(several),
                });
            }
        },
    };
    match &selected.selection {
        EntrySelection::Located(_) => Ok(selected),
        EntrySelection::Unaddressable(reason) => Err(SmartTacticSelectionError {
            reason: reason.clone(),
            candidates: Vec::new(),
        }),
    }
}

/// Whether two entries select the same expansion.
fn same_selection(left: &EntrySelection, right: &EntrySelection) -> bool {
    match (left, right) {
        (EntrySelection::Located(left), EntrySelection::Located(right)) => {
            left.site == right.site
                && left.source_index == right.source_index
                && left.nested == right.nested
        }
        _ => false,
    }
}

fn locate_source_tactic_file(
    click_source: &str,
    file: &ClickFile,
    line: usize,
    column: usize,
) -> Result<LocatedSourceTactic, ClickError> {
    let entries = source_tactic_entries(click_source, file)?;
    // The library entry point also expands a non-smart tactic named by its
    // exact start (a `have` whose explicit body a smart step closes, a whole
    // pure theorem proof); every other location selects the innermost smart
    // tactic containing it.
    let wanted = offset_at_position(click_source, line, column)?;
    let exact = entries
        .iter()
        .filter(|entry| {
            entry.anchor == wanted && matches!(entry.selection, EntrySelection::Located(_))
        })
        .min_by_key(|entry| entry.span.end - entry.span.start);
    let entry = match exact {
        Some(entry) => entry,
        None => select_source_tactic_entry(click_source, &entries, line, Some(column))
            .map_err(|error| error.into_click_error(line, Some(column)))?,
    };
    // A stale note from an earlier expansion on this thread must not widen
    // this one.
    EXPANSION_REPLACES_FROM.with(|from| from.set(None));
    match &entry.selection {
        EntrySelection::Located(located) => {
            let mut located = located.clone();
            located.sibling_starts = entries
                .iter()
                .filter_map(|entry| match &entry.selection {
                    EntrySelection::Located(sibling)
                        if sibling.site == located.site && sibling.nested.is_empty() =>
                    {
                        Some((sibling.source_index, entry.span.start))
                    }
                    _ => None,
                })
                .collect();
            located.function_block = match &located.site {
                ProofSite::FunctionClaim { function_name, .. } => proof_function_blocks(file)
                    .find(|block| block.signature().name() == function_name)
                    .cloned(),
                ProofSite::TheoremEnsure { .. } => None,
            };
            Ok(located)
        }
        EntrySelection::Unaddressable(reason) => Err(ClickError::new(reason.clone())),
    }
}

/// Records every written tactic of every selected proof, keyed by span.
fn source_tactic_entries(
    click_source: &str,
    file: &ClickFile,
) -> Result<Vec<SourceTacticEntry>, ClickError> {
    let source_tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let tokens = ProofTokens::new(file, &source_tokens);
    source_tactic_entries_with_tokens(file, &tokens)
}

fn source_tactic_entries_with_tokens(
    file: &ClickFile,
    tokens: &ProofTokens<'_>,
) -> Result<Vec<SourceTacticEntry>, ClickError> {
    let mut entries = Vec::new();
    let declarations = DeclarationSources::new(tokens);
    for theorem in file.theorem_definitions() {
        // An axiom has no proof to expand.
        if theorem.is_axiom() || !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        let source = declarations.theorem(theorem)?;
        let kernel_axiom_name = proof::is_kernel_standard_theorem_name(theorem.name())
            && theorem.parameters().iter().all(|parameter| {
                parameter.click_type() == &ClickType::Program(InterfaceType::Int32)
            });
        for (ensure_index, ensure) in theorem.ensures().iter().enumerate() {
            if kernel_axiom_name
                && !matches!(
                    ensure.ensure(),
                    Ensure::Proposition(ClickProposition::PredicateCall { .. })
                )
            {
                continue;
            }
            let edit = find_ensure_proof_edit(tokens, &source, ensure_index)?;
            let label = theorem.ensure_claim_label(ensure_index);
            let site = ProofSite::TheoremEnsure {
                theorem_name: theorem.name().to_string(),
                ensure_index,
            };
            proof_tactic_entries(tokens, &edit, ensure.proof(), &site, &label, &mut entries)?;
        }
    }
    for function_block in proof_function_blocks(file) {
        if function_block.is_external() {
            continue;
        }
        let function_name = function_block.signature().name();
        let function = declarations.function(function_block)?;
        if let Some(proof) = expansion_covering_proof(function_block) {
            let edit = find_grouped_proof_edit(tokens, &function, function_block)?;
            proof_tactic_entries(
                tokens,
                &edit,
                proof,
                &ProofSite::FunctionClaim {
                    function_name: function_name.to_string(),
                    claim: ContractProofClaim::Grouped,
                },
                &function_block.contract_claim_label(),
                &mut entries,
            )?;
        }
        for (index, ensure) in function_block.ensures().iter().enumerate() {
            if function_block.covers_claim_proof(ensure.proof()) {
                continue;
            }
            let claim = ContractProofClaim::Ensure(index);
            let edit = find_claim_proof_edit(tokens, &function, function_block, claim)?;
            let label = function_block.ensure_claim_label(index);
            proof_tactic_entries(
                tokens,
                &edit,
                ensure.proof(),
                &ProofSite::FunctionClaim {
                    function_name: function_name.to_string(),
                    claim,
                },
                &label,
                &mut entries,
            )?;
        }
        for (index, ensure) in function_block.exceptional_ensures().iter().enumerate() {
            if function_block.covers_claim_proof(ensure.proof()) {
                continue;
            }
            let claim = ContractProofClaim::ExceptionalEnsure(index);
            let edit = find_claim_proof_edit(tokens, &function, function_block, claim)?;
            let label = function_block.exceptional_ensure_claim_label(index);
            proof_tactic_entries(
                tokens,
                &edit,
                ensure.proof(),
                &ProofSite::FunctionClaim {
                    function_name: function_name.to_string(),
                    claim,
                },
                &label,
                &mut entries,
            )?;
        }
    }
    Ok(entries)
}

/// A written one-tactic proof owns its `by` clause when expanded: a
/// structured certificate or several generated steps need a real block.
/// The lexer already marks its implicit opening brace with an empty span.
fn written_tactic_source_edit(
    tokens: &ProofTokens<'_>,
    start: usize,
    span: Range<usize>,
) -> Result<TacticSourceEdit, ClickError> {
    if let Some(open) = start.checked_sub(1)
        && tokens[open].text == "{"
        && tokens[open].span.is_empty()
        && let Some(by) = open.checked_sub(1)
        && tokens[by].text == "by"
    {
        return Ok(TacticSourceEdit::PartialProofClause(
            tokens.blocks.clauses.at(by)?.span(tokens),
        ));
    }
    Ok(TacticSourceEdit::Partial(span))
}

fn proof_tactic_entries(
    tokens: &ProofTokens<'_>,
    edit: &ProofSourceEdit,
    proof: &SourceProof,
    site: &ProofSite,
    claim_label: &str,
    entries: &mut Vec<SourceTacticEntry>,
) -> Result<(), ClickError> {
    let whole_proof = |span: Range<usize>, anchor: usize, name: &str| SourceTacticEntry {
        span,
        anchor,
        claim_label: claim_label.to_string(),
        tactic_name: name.to_string(),
        smart: true,
        has_implicit_obligations: false,
        selection: EntrySelection::Located(LocatedSourceTactic {
            site: site.clone(),
            source_index: 0,
            nested: Vec::new(),
            edit: TacticSourceEdit::WholeProof(edit.clone()),
            sibling_starts: Vec::new(),
            function_block: None,
            source_spans: tokens.spans.clone(),
        }),
    };
    let omitted_proof_span = || match edit {
        ProofSourceEdit::DefaultTerminator { span, selector } => *selector..span.end,
        _ => tokens
            .iter()
            .find(|token| token.span.start == edit.selector())
            .map_or(edit.selector()..edit.selector() + 1, |token| {
                token.span.clone()
            }),
    };
    match proof {
        SourceProof::Script(tactics) => {
            let ProofSourceEdit::Explicit(source_proof_span) = edit else {
                return Err(ClickError::new(
                    "an explicit proof script has no source `by` clause",
                ));
            };
            let flat = collect_source_tactics(tokens, source_proof_span, tactics)?;
            // The implicit tail follows the last written tactic and numbers
            // after it, as the script runner appends it. Its site is the
            // script's closing brace.
            let tail = (super::proof::script_ends_with_implicit_tail(tactics)
                && source_proof_span.end > source_proof_span.start)
                .then(|| flat.last().map(|item| (flat.len(), item.span.end)))
                .flatten();
            for (source_index, item) in flat.into_iter().enumerate() {
                let (tactic_name, smart, edit) = match item.tactic {
                    FlatTactic::Written(tactic) => (
                        tactic_name(tactic).to_string(),
                        source_site_kind(tactic) == SourceSiteKind::ExpandableAutomation,
                        written_tactic_source_edit(tokens, item.tokens.start, item.span.clone())?,
                    ),
                    FlatTactic::Phase(tactic, by) => {
                        // A frontier-local loop phase proved by one smart
                        // tactic is rewritten as the whole `by` clause.
                        (
                            smart_tactic_name(tactic).to_string(),
                            true,
                            TacticSourceEdit::PartialProofClause(
                                tokens.blocks.clauses.at(by)?.span(tokens),
                            ),
                        )
                    }
                };
                let entry = SourceTacticEntry {
                    span: item.span.clone(),
                    anchor: item.span.start,
                    claim_label: claim_label.to_string(),
                    tactic_name,
                    smart,
                    has_implicit_obligations: matches!(
                        item.tactic,
                        FlatTactic::Written(ProofTactic::ApplyTheorem(_))
                    ),
                    selection: EntrySelection::Located(LocatedSourceTactic {
                        site: site.clone(),
                        source_index,
                        nested: Vec::new(),
                        edit,
                        sibling_starts: Vec::new(),
                        function_block: None,
                        source_spans: tokens.spans.clone(),
                    }),
                };
                entries.push(entry.clone());
                if let FlatTactic::Written(tactic) = item.tactic
                    && smart
                {
                    smart_container_alias_entries(
                        tokens,
                        item.tokens.clone(),
                        tactic,
                        &entry,
                        entries,
                    );
                }
                // A smart `have` is one site: its body belongs to it.
                if let FlatTactic::Written(ProofTactic::Have(have)) = item.tactic
                    && !smart
                {
                    have_body_tactic_entries(
                        tokens,
                        item.tokens.clone(),
                        have,
                        site,
                        claim_label,
                        source_index,
                        &[],
                        entries,
                    )?;
                }
                // An `all` block counts as one claim-level tactic; the
                // tactics in its arms are addressed by arm and written
                // position below it, as the script runner reports them.
                let arms = match item.tactic {
                    FlatTactic::Written(ProofTactic::All(all)) if !smart => Some(
                        tokens
                            .cases_arms(&item.tokens)?
                            .into_iter()
                            .zip(all.arms.iter().map(|arm| arm.tactics.as_slice()))
                            .collect::<Vec<_>>(),
                    ),
                    FlatTactic::Written(ProofTactic::IntroBlock { body, .. }) if !smart => Some(
                        vec![(tokens.body_block(&item.tokens, "intro")?, body.as_slice())],
                    ),
                    _ => None,
                };
                if let Some(arms) = arms {
                    for (arm, ((open, close), tactics)) in arms.into_iter().enumerate() {
                        block_tactic_entries(
                            tokens,
                            &WrittenBlock {
                                open,
                                close,
                                tactics,
                                prefix: &[arm],
                            },
                            site,
                            claim_label,
                            source_index,
                            entries,
                        )?;
                    }
                }
            }
            if let Some((source_index, at)) = tail {
                let close = source_proof_span.end - 1;
                entries.push(SourceTacticEntry {
                    span: close..source_proof_span.end,
                    anchor: close,
                    claim_label: claim_label.to_string(),
                    tactic_name: "implicit tail".to_string(),
                    smart: true,
                    has_implicit_obligations: false,
                    selection: EntrySelection::Located(LocatedSourceTactic {
                        site: site.clone(),
                        source_index,
                        nested: Vec::new(),
                        edit: TacticSourceEdit::Append(at),
                        sibling_starts: Vec::new(),
                        function_block: None,
                        source_spans: tokens.spans.clone(),
                    }),
                });
            }
            Ok(())
        }
        SourceProof::Tactic(tactic) => {
            let name = smart_tactic_name(*tactic);
            match edit {
                ProofSourceEdit::Explicit(proof_span) => {
                    let by = tokens
                        .binary_search_by_key(&proof_span.start, |token| token.span.start)
                        .ok()
                        .filter(|index| tokens[*index].text == "by")
                        .ok_or_else(|| ClickError::new("could not locate source `by` clause"))?;
                    let anchor = tokens
                        .get(by + 1)
                        .map_or(proof_span.start, |token| token.span.start);
                    entries.push(whole_proof(proof_span.clone(), anchor, name));
                }
                ProofSourceEdit::DefaultTerminator { .. }
                | ProofSourceEdit::OmittedLoopPhase { .. } => {
                    entries.push(whole_proof(omitted_proof_span(), edit.selector(), name));
                }
            }
            Ok(())
        }
        SourceProof::Default => {
            entries.push(whole_proof(
                omitted_proof_span(),
                edit.selector(),
                "implicit tail",
            ));
            Ok(())
        }
    }
}

fn smart_tactic_name(tactic: SmartTactic) -> &'static str {
    match tactic {
        SmartTactic::ImplicitTail => "implicit tail",
        SmartTactic::Solve => "solve",
    }
}

/// Records the tactics written in a non-smart `have` body, addressed by the
/// `have`'s claim-level source index and their written positions.
#[allow(clippy::too_many_arguments)]
fn have_body_tactic_entries(
    tokens: &ProofTokens<'_>,
    have_tokens: Range<usize>,
    have: &ProofHave,
    site: &ProofSite,
    claim_label: &str,
    source_index: usize,
    prefix: &[usize],
    entries: &mut Vec<SourceTacticEntry>,
) -> Result<(), ClickError> {
    let SourceProof::Script(body) = &have.proof else {
        return Ok(());
    };
    let (open, close) = tokens.body_block(&have_tokens, "have")?;
    let block = WrittenBlock {
        open,
        close,
        tactics: body,
        prefix,
    };
    block_tactic_entries(tokens, &block, site, claim_label, source_index, entries)
}

/// One written block of tactics below a claim-level tactic: a `have` body
/// or an arm of a structured tactic, with the source path prefix its
/// tactics' positions extend.
struct WrittenBlock<'b> {
    open: usize,
    close: usize,
    tactics: &'b [ProofTactic],
    prefix: &'b [usize],
}

/// Records each tactic written directly in `block` at its source path, the
/// same path the proof step that checks it reports, and descends into the
/// blocks it writes: a non-smart `have` body, and each arm of a proof `if`
/// or `cases`.
fn block_tactic_entries(
    tokens: &ProofTokens<'_>,
    block: &WrittenBlock<'_>,
    site: &ProofSite,
    claim_label: &str,
    source_index: usize,
    entries: &mut Vec<SourceTacticEntry>,
) -> Result<(), ClickError> {
    let direct = tokens.tactic_ranges(block.open, block.close)?;
    if direct.len() != block.tactics.len() {
        return Err(ClickError::new(format!(
            "source block has {} direct tactic(s), but the parsed block has {}",
            direct.len(),
            block.tactics.len()
        )));
    }
    for (position, (tactic, token_range)) in block.tactics.iter().zip(direct).enumerate() {
        let span = tokens[token_range.start].span.start..tokens[token_range.end - 1].span.end;
        let mut path = block.prefix.to_vec();
        path.push(position);
        let smart = source_site_kind(tactic) == SourceSiteKind::ExpandableAutomation;
        let entry = SourceTacticEntry {
            span: span.clone(),
            anchor: span.start,
            claim_label: claim_label.to_string(),
            tactic_name: tactic_name(tactic).to_string(),
            smart,
            has_implicit_obligations: matches!(tactic, ProofTactic::ApplyTheorem(_)),
            selection: EntrySelection::Located(LocatedSourceTactic {
                site: site.clone(),
                source_index,
                nested: path.clone(),
                edit: written_tactic_source_edit(tokens, token_range.start, span.clone())?,
                sibling_starts: Vec::new(),
                function_block: None,
                source_spans: tokens.spans.clone(),
            }),
        };
        entries.push(entry.clone());
        if smart {
            smart_container_alias_entries(tokens, token_range.clone(), tactic, &entry, entries);
            continue;
        }
        let arms: Option<Vec<&[ProofTactic]>> = match tactic {
            ProofTactic::IntroBlock { body, .. } => Some(vec![body]),
            ProofTactic::If(proof_if) => Some(vec![&proof_if.then_tactics, &proof_if.else_tactics]),
            ProofTactic::Cases(cases) => {
                Some(cases.arms().iter().map(|arm| arm.tactics()).collect())
            }
            ProofTactic::All(all) => {
                Some(all.arms.iter().map(|arm| arm.tactics.as_slice()).collect())
            }
            ProofTactic::Both(both) => Some(vec![&both.left_tactics, &both.right_tactics]),
            _ => None,
        };
        match (tactic, arms) {
            (ProofTactic::Have(have), _) => have_body_tactic_entries(
                tokens,
                token_range,
                have,
                site,
                claim_label,
                source_index,
                &path,
                entries,
            )?,
            // An arm tactic's path names the arm, then its position there.
            (_, Some(arms)) => {
                let blocks = structured_tactic_arm_blocks(tokens, token_range.clone())?
                    .ok_or_else(|| {
                        ClickError::new("could not locate the arms of a source structured tactic")
                    })?;
                for (arm, ((open, close), tactics)) in blocks.into_iter().zip(arms).enumerate() {
                    let mut prefix = path.clone();
                    prefix.push(arm);
                    let arm_block = WrittenBlock {
                        open,
                        close,
                        tactics,
                        prefix: &prefix,
                    };
                    block_tactic_entries(
                        tokens,
                        &arm_block,
                        site,
                        claim_label,
                        source_index,
                        entries,
                    )?;
                }
            }
            // The linear body runner checks no other structured tactic, so a
            // smart tactic written inside one has no checked occurrence of
            // its own. Say so rather than selecting a neighbor.
            _ if tactic_contains_smart_tactic(tactic) => {
                entries.push(SourceTacticEntry {
                    span: span.clone(),
                    anchor: span.start,
                    claim_label: claim_label.to_string(),
                    tactic_name: tactic_name(tactic).to_string(),
                    smart: true,
                    has_implicit_obligations: false,
                    selection: EntrySelection::Unaddressable(format!(
                        "the location is inside a proof `{}` written in a `have` body, which the `have` body checker does not run, so a smart tactic there has no checked occurrence of its own; expand the enclosing claim with `--claim {claim_label}`",
                        tactic_name(tactic)
                    )),
                });
            }
            _ => {}
        }
    }
    Ok(())
}

/// Records each smart tactic written inside a smart site that owns its body
/// (a smart `have`, `both`, or `close_invariants() by`) as an alias selecting
/// that site: the body is expanded as part of the site, never on its own.
fn smart_container_alias_entries(
    tokens: &ProofTokens<'_>,
    tactic_tokens: Range<usize>,
    tactic: &ProofTactic,
    container: &SourceTacticEntry,
    entries: &mut Vec<SourceTacticEntry>,
) {
    let body = |range: Range<usize>| tokens.child_blocks(&range).first().copied();
    let mut blocks: Vec<((usize, usize), &[ProofTactic])> = Vec::new();
    match tactic {
        ProofTactic::Have(have) => match &have.proof {
            SourceProof::Script(script) => {
                if let Some(block) = body(tactic_tokens) {
                    blocks.push((block, script));
                }
            }
            SourceProof::Tactic(smart) => {
                // The one-tactic proof `by T();` is the implicit block the
                // parser recorded; its zero-width `{` stands at the call.
                if let Some((open, _)) = body(tactic_tokens) {
                    let token = &tokens[open];
                    entries.push(SourceTacticEntry {
                        span: token.span.clone(),
                        anchor: token.span.start,
                        tactic_name: smart_tactic_name(*smart).to_string(),
                        ..container.clone()
                    });
                }
            }
            SourceProof::Default => {}
        },
        ProofTactic::IntroBlock { body: script, .. }
        | ProofTactic::CloseInvariantsBy(script)
        | ProofTactic::StepProved {
            proof: StepProof::By(script),
            ..
        } => {
            if let Some(block) = body(tactic_tokens) {
                blocks.push((block, script));
            }
        }
        ProofTactic::All(all) => {
            if let Ok(arms) = tokens.cases_arms(&tactic_tokens) {
                blocks.extend(
                    arms.into_iter()
                        .zip(all.arms.iter().map(|arm| arm.tactics.as_slice())),
                );
            }
        }
        _ => {}
    }
    for ((open, close), body) in blocks {
        let Ok(direct) = tokens.tactic_ranges(open, close) else {
            continue;
        };
        if direct.len() != body.len() {
            continue;
        }
        for (inner, range) in body.iter().zip(direct) {
            let span = tokens[range.start].span.start..tokens[range.end - 1].span.end;
            if source_site_kind(inner) == SourceSiteKind::ExpandableAutomation {
                entries.push(SourceTacticEntry {
                    span: span.clone(),
                    anchor: span.start,
                    tactic_name: tactic_name(inner).to_string(),
                    ..container.clone()
                });
            }
            smart_container_alias_entries(tokens, range, inner, container, entries);
        }
    }
}

/// Whether a smart tactic is written anywhere inside `tactic`.
fn tactic_contains_smart_tactic(tactic: &ProofTactic) -> bool {
    // A loop proof left out is the default proof, which is smart.
    if let ProofTactic::Loop(clause) = tactic
        && (clause.initialize_proof().is_none() || clause.preserve_proof().is_none())
    {
        return true;
    }
    tactic.children().into_iter().any(|child| {
        let (TacticChild::Continuing(proof) | TacticChild::Obligation(proof)) = child;
        // A default or smart-tactic proof is itself smart.
        proof.tactics().is_none_or(|tactics| {
            tactics.iter().any(|tactic| {
                source_site_kind(tactic) == SourceSiteKind::ExpandableAutomation
                    || tactic_contains_smart_tactic(tactic)
            })
        })
    })
}

pub fn c_tactic_source_position(
    click_source: &str,
    c_sources: &[(&str, &str)],
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    tactic_source_position(
        click_source,
        &ProgramInputs::Bundle(c_sources.to_vec()),
        claim_label,
        source_index,
    )
}

pub fn tactic_source_position(
    click_source: &str,
    inputs: &ProgramInputs<'_>,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = ProgramSourceContext::of(inputs)?;
    tactic_source_position_context(&sources, click_source, claim_label, source_index)
}

/// Where the Click declaration named `name` is written: a function block,
/// a named contract or a theorem. The position is the first token of the
/// line the name is on, so the excerpt starts at the return type or
/// keyword. `None` when the source declares no such name.
///
/// A failure with no tactic or C statement to address, such as a contract
/// that could not be set up at entry, shows this declaration instead. A
/// declaration is the name followed by its parameters or body outside every
/// brace; a use of the name inside a body is not one.
pub fn click_declaration_source_position(click_source: &str, name: &str) -> Option<SourcePosition> {
    let tokens = plain_source_tokens(click_source).ok()?;
    let mut depth = 0usize;
    let declared = tokens.iter().enumerate().find_map(|(index, token)| {
        match token.text.as_str() {
            "{" => depth += 1,
            "}" => depth = depth.saturating_sub(1),
            text if depth == 0
                && (text == name
                    || (name.contains("::")
                        && name.rsplit("::").next() == Some(text)
                        && rust_path_ending_at(&tokens, index).join("::") == name)) =>
            {
                // A generic declaration lists its type parameters between
                // the name and the parameter list.
                let mut next = index + 1;
                if tokens.get(next).map(|token| token.text.as_str()) == Some("<") {
                    next = tokens[next..]
                        .iter()
                        .position(|token| token.text == ">")
                        .map_or(next, |close| next + close + 1);
                }
                // A function, contract, resource or theorem is followed by
                // its parameters; a datatype by its body.
                if matches!(
                    tokens.get(next).map(|token| token.text.as_str()),
                    Some("(" | "{")
                ) {
                    return Some(token.span.start);
                }
            }
            _ => {}
        }
        None
    })?;
    let line_start = click_source[..declared]
        .rfind('\n')
        .map_or(0, |newline| newline + 1);
    let first_token = tokens
        .iter()
        .find(|token| token.span.start >= line_start)?
        .span
        .start;
    Some(position_at_offset(click_source, first_token))
}

pub fn project_tactic_source_position(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    tactic_source_position_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
        source_index,
    )
}

pub fn project_tactic_source_positions(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    claim_label: &str,
) -> Result<Vec<SourcePosition>, ClickError> {
    let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    tactic_source_positions_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
    )
}

fn tactic_source_position_context(
    c_sources: &ProgramSourceContext<'_>,
    click_source: &str,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let file = parse_source_with_program_layouts_context(click_source, c_sources)?;
    tactic_source_position_file(&file, click_source, claim_label, source_index)
}

fn tactic_source_position_file(
    file: &ClickFile,
    click_source: &str,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let offsets = tactic_source_offsets_with_tokens(file, claim_label, &tokens)?;
    offsets
        .get(source_index)
        .map(|offset| positions_at_offsets(click_source, [*offset])[0].clone())
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` has no source tactic occurrence {source_index}"
            ))
        })
}

#[cfg(test)]
mod selected_source_position_tests {
    use super::*;

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/surface/expansion/selected_source_position_tests.rs");
    }
}

/// Resolve many byte offsets with one source walk, preserving request order.
/// In particular, a long line containing many tactics must not be rescanned
/// from its start for each tactic's character column.
fn positions_at_offsets(
    source: &str,
    offsets: impl IntoIterator<Item = usize>,
) -> Vec<SourcePosition> {
    let mut ordered: Vec<_> = offsets.into_iter().enumerate().collect();
    ordered.sort_unstable_by_key(|(_, offset)| *offset);
    let mut positions = vec![SourcePosition::new(1, 1); ordered.len()];
    let mut chars = source.char_indices().peekable();
    let mut line = 1;
    let mut column = 1;
    for (index, offset) in ordered {
        crate::instrumentation::record_deterministic_work(1);
        while let Some(&(at, character)) = chars.peek() {
            if at >= offset {
                break;
            }
            chars.next();
            crate::instrumentation::record_deterministic_work(1);
            if character == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
        }
        positions[index] = SourcePosition::new(line, column);
    }
    positions
}

/// A Rust function or C++ declaration is named by its path,
/// `quad::walk.contract`, `Square::area.contract` or `fee<true>.contract`,
/// or by the name the importer gives it; this is the label under the
/// importer's name.
fn resolve_source_claim_label<'a>(
    file: &ClickFile,
    claim_label: &'a str,
) -> std::borrow::Cow<'a, str> {
    if let Some((function, rest)) = claim_label.split_once('.')
        && !function
            .chars()
            .all(|character| character.is_ascii_alphanumeric() || character == '_')
        && let Some(block) = file.function_blocks().iter().find(|block| {
            crate::languages::source_display_name(block.signature().name()).as_deref()
                == Some(function)
        })
    {
        return format!("{}.{rest}", block.signature().name()).into();
    }
    claim_label.into()
}

fn tactic_source_positions_file(
    file: &ClickFile,
    click_source: &str,
    claim_label: &str,
) -> Result<Vec<SourcePosition>, ClickError> {
    let tokens = proof_source_tokens(click_source, &file.source_spans().implicit_proofs)?;
    let offsets = tactic_source_offsets_with_tokens(file, claim_label, &tokens)?;
    Ok(positions_at_offsets(click_source, offsets))
}

fn tactic_source_offsets_with_tokens(
    file: &ClickFile,
    claim_label: &str,
    tokens: &[SourceToken],
) -> Result<Vec<usize>, ClickError> {
    tactic_source_offsets(file, claim_label, &ProofTokens::new(file, tokens))
}

fn tactic_source_offsets(
    file: &ClickFile,
    claim_label: &str,
    tokens: &ProofTokens<'_>,
) -> Result<Vec<usize>, ClickError> {
    let claim_label = &*resolve_source_claim_label(file, claim_label);
    let declarations = DeclarationSources::new(tokens);
    if claim_label == "program.termination" {
        let (start, end) = file
            .termination_span
            .as_ref()
            .ok_or_else(|| ClickError::new("the program termination proof is omitted"))?;
        let first = declarations
            .token_at(start, Some("termination"))
            .expect("parser recorded termination keyword");
        let last = declarations
            .token_at(end, Some("}"))
            .expect("parser recorded termination block");
        let span = tokens[first + 1].span.start..tokens[last].span.end;
        let tactics = file
            .termination_proof
            .as_ref()
            .expect("the parsed termination block");
        return Ok(collect_source_tactic_spans(tokens, &span, tactics)?
            .iter()
            .map(|span| span.start)
            .collect());
    }
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        for (ensure_index, ensure) in theorem.ensures().iter().enumerate() {
            let execution_claim = theorem.executes.is_some()
                && ensure_index == 0
                && claim_label == claim_labels::contract_claim_label(theorem.name());
            if theorem.ensure_claim_label(ensure_index) != claim_label && !execution_claim {
                continue;
            }
            let source = declarations.theorem(theorem)?;
            let edit = find_ensure_proof_edit(tokens, &source, ensure_index)?;
            return proof_source_offsets(
                tokens,
                match &edit {
                    ProofSourceEdit::Explicit(span) => Some(span),
                    ProofSourceEdit::DefaultTerminator { .. }
                    | ProofSourceEdit::OmittedLoopPhase { .. } => None,
                },
                Some(ensure.proof()),
                edit.selector(),
                claim_label,
            );
        }
    }
    for tactic in file.tactic_definitions() {
        if !file.function_is_selected(tactic.name()) {
            continue;
        }
        if claim_label != tactic.function_block().contract_claim_label() {
            continue;
        }
        let function = declarations.function(tactic.function_block())?;
        return proof_source_offsets(
            tokens,
            Some(&find_grouped_proof_span(tokens, &function)?),
            tactic.function_block().grouped_proof(),
            tokens[function.body_close].span.start,
            claim_label,
        );
    }
    for function_block in proof_function_blocks(file) {
        let selected =
            function_expansion_claim_by_label(function_block, claim_label).and_then(|claim| {
                match claim {
                    ContractProofClaim::Grouped => {
                        expansion_covering_proof(function_block).map(|proof| (claim, proof))
                    }
                    ContractProofClaim::Ensure(index) => function_block
                        .ensures()
                        .get(index)
                        .map(|ensure| (claim, ensure.proof())),
                    ContractProofClaim::ExceptionalEnsure(index) => function_block
                        .exceptional_ensures()
                        .get(index)
                        .map(|ensure| (claim, ensure.proof())),
                }
            });
        let Some((claim, proof)) = selected else {
            continue;
        };
        let function = declarations.function(function_block)?;
        let fallback = match claim {
            ContractProofClaim::Grouped => tokens[function.body_close].span.start,
            ContractProofClaim::Ensure(_) | ContractProofClaim::ExceptionalEnsure(_) => {
                find_claim_clause_offset(tokens, &function, function_block, claim)?
            }
        };
        let proof_span = match claim {
            ContractProofClaim::Grouped => {
                match find_grouped_proof_edit(tokens, &function, function_block)? {
                    ProofSourceEdit::Explicit(span) => Some(span),
                    ProofSourceEdit::DefaultTerminator { .. }
                    | ProofSourceEdit::OmittedLoopPhase { .. } => None,
                }
            }
            ContractProofClaim::Ensure(_) | ContractProofClaim::ExceptionalEnsure(_) => {
                find_claim_proof_span(tokens, &function, function_block, claim).ok()
            }
        };
        return proof_source_offsets(
            tokens,
            proof_span.as_ref(),
            Some(proof),
            fallback,
            claim_label,
        );
    }
    Err(ClickError::new(format!(
        "could not locate source proof `{claim_label}`"
    )))
}

fn proof_source_offsets(
    tokens: &ProofTokens<'_>,
    proof_span: Option<&Range<usize>>,
    proof: Option<&SourceProof>,
    fallback: usize,
    claim_label: &str,
) -> Result<Vec<usize>, ClickError> {
    if let Some(tactics) = proof.and_then(SourceProof::tactics) {
        let proof_span = proof_span.ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` has no explicit source proof clause"
            ))
        })?;
        let spans = collect_source_tactic_spans(tokens, proof_span, tactics)?;
        return Ok(spans.iter().map(|span| span.start).collect());
    }
    if let Some(proof_span) = proof_span {
        let by = tokens
            .binary_search_by_key(&proof_span.start, |token| token.span.start)
            .ok()
            .filter(|index| tokens[*index].text == "by")
            .ok_or_else(|| ClickError::new("could not locate source `by` clause"))?;
        if let Some(tactic) = tokens.get(by + 1) {
            return Ok(vec![tactic.span.start]);
        }
    }
    Ok(vec![fallback])
}

fn find_claim_clause_offset(
    tokens: &[SourceToken],
    function: &FunctionSource,
    function_block: &FunctionBlock,
    claim: ContractProofClaim,
) -> Result<usize, ClickError> {
    Ok(find_claim_proof_edit(tokens, function, function_block, claim)?.selector())
}

pub(super) fn parse_source_with_c_layouts(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<ClickFile, ClickError> {
    let sources = ProgramSourceContext::bundle(c_sources);
    parse_source_with_program_layouts_context(click_source, &sources)
}

fn parse_source_with_program_layouts_context(
    click_source: &str,
    sources: &ProgramSourceContext<'_>,
) -> Result<ClickFile, ClickError> {
    let layouts = parse_c_layouts(click_source, sources)?;
    parser::parse_with_interface_catalog(click_source, layouts, sources.library_contracts())
}

fn offset_at_position(source: &str, line: usize, column: usize) -> Result<usize, ClickError> {
    if line == 0 || column == 0 {
        return Err(ClickError::new("source lines and columns are one-based"));
    }
    let mut line_start = 0;
    for current_line in 1..line {
        let Some(newline) = source[line_start..].find('\n') else {
            return Err(ClickError::new(format!("source has no line {line}")));
        };
        line_start += newline + 1;
        if current_line + 1 == line {
            break;
        }
    }
    let line_end = source[line_start..]
        .find('\n')
        .map_or(source.len(), |newline| line_start + newline);
    let line_source = &source[line_start..line_end];
    let byte_in_line = if column == 1 {
        0
    } else {
        line_source
            .char_indices()
            .nth(column - 1)
            .map(|(offset, _)| offset)
            .ok_or_else(|| ClickError::new(format!("line {line} has no column {column}")))?
    };
    Ok(line_start + byte_in_line)
}

/// The written arm blocks, as `(open, close)` token pairs, of a proof `if`,
/// `cases`, `all`, or `intro` tactic; `None` for any other tactic.
fn structured_tactic_arm_blocks(
    tokens: &ProofTokens<'_>,
    range: Range<usize>,
) -> Result<Option<Vec<(usize, usize)>>, ClickError> {
    Ok(match tokens[range.start].text.as_str() {
        "if" => Some(tokens.two_arms(&range, "if")?.to_vec()),
        "cases" | "all" => Some(tokens.cases_arms(&range)?),
        "intro" => Some(vec![tokens.body_block(&range, "intro")?]),
        _ => None,
    })
}

pub(super) fn position_at_offset(source: &str, offset: usize) -> SourcePosition {
    let prefix = &source[..offset];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let line_start = prefix.rfind('\n').map_or(0, |newline| newline + 1);
    let column = source[line_start..offset].chars().count() + 1;
    SourcePosition::new(line, column)
}

fn collect_source_tactic_spans(
    tokens: &ProofTokens<'_>,
    proof_span: &Range<usize>,
    tactics: &[ProofTactic],
) -> Result<Vec<Range<usize>>, ClickError> {
    Ok(collect_source_tactics(tokens, proof_span, tactics)?
        .into_iter()
        .map(|tactic| tactic.span)
        .collect())
}

/// One claim-level source tactic, in the flat pre-order numbering that
/// timing, profiling, audit, and expansion share.
struct FlatSourceTactic<'t> {
    span: Range<usize>,
    /// The tactic's token range, end exclusive.
    tokens: Range<usize>,
    tactic: FlatTactic<'t>,
}

#[derive(Clone, Copy)]
enum FlatTactic<'t> {
    Written(&'t ProofTactic),
    /// A frontier-local loop phase proved by one smart tactic (`by close()`).
    Phase(SmartTactic, usize),
}

fn collect_source_tactics<'t>(
    tokens: &ProofTokens<'_>,
    proof_span: &Range<usize>,
    tactics: &'t [ProofTactic],
) -> Result<Vec<FlatSourceTactic<'t>>, ClickError> {
    let by = tokens
        .binary_search_by_key(&proof_span.start, |token| token.span.start)
        .ok()
        .filter(|index| tokens[*index].text == "by")
        .ok_or_else(|| ClickError::new("could not locate selected source proof"))?;
    let open = by + 1;
    if tokens.get(open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new(
            "individual tactic expansion requires an explicit `by { ... }` proof",
        ));
    }
    let close = tokens.block_close(open)?;
    let mut spans = Vec::new();
    collect_tactic_block_spans(tokens, open, close, tactics, &mut spans)?;
    Ok(spans)
}

fn collect_tactic_block_spans<'t>(
    tokens: &ProofTokens<'_>,
    open: usize,
    close: usize,
    tactics: &'t [ProofTactic],
    spans: &mut Vec<FlatSourceTactic<'t>>,
) -> Result<(), ClickError> {
    let direct = tokens.tactic_ranges(open, close)?;
    if direct.len() != tactics.len() {
        return Err(ClickError::new(format!(
            "source proof has {} direct tactic(s), but the parsed proof has {}",
            direct.len(),
            tactics.len()
        )));
    }
    for (tactic, token_range) in tactics.iter().zip(direct) {
        spans.push(FlatSourceTactic {
            span: tokens[token_range.start].span.start..tokens[token_range.end - 1].span.end,
            tokens: token_range.clone(),
            tactic: FlatTactic::Written(tactic),
        });
        match tactic {
            ProofTactic::Open(proof_open) => {
                let (body_open, body_close) = tokens.body_block(&token_range, "with")?;
                collect_tactic_block_spans(
                    tokens,
                    body_open,
                    body_close,
                    &proof_open.tactics,
                    spans,
                )?;
            }
            ProofTactic::If(proof_if) => {
                let [(then_open, then_close), (else_open, else_close)] =
                    tokens.two_arms(&token_range, "if")?;
                collect_tactic_block_spans(
                    tokens,
                    then_open,
                    then_close,
                    &proof_if.then_tactics,
                    spans,
                )?;
                collect_tactic_block_spans(
                    tokens,
                    else_open,
                    else_close,
                    &proof_if.else_tactics,
                    spans,
                )?;
            }
            ProofTactic::Branch(proof_branch) => {
                let [(then_open, then_close), (else_open, else_close)] =
                    tokens.labeled_arms(&token_range, ["true", "false"])?;
                collect_tactic_block_spans(
                    tokens,
                    then_open,
                    then_close,
                    &proof_branch.then_tactics,
                    spans,
                )?;
                collect_tactic_block_spans(
                    tokens,
                    else_open,
                    else_close,
                    &proof_branch.else_tactics,
                    spans,
                )?;
            }
            ProofTactic::All(all) => {
                let blocks = tokens.cases_arms(&token_range)?;
                if blocks.len() != all.arms.len() {
                    return Err(ClickError::new(
                        "source `all` arms do not match the parsed proof",
                    ));
                }
                for ((open, close), arm) in blocks.into_iter().zip(&all.arms) {
                    collect_tactic_block_spans(tokens, open, close, &arm.tactics, spans)?;
                }
            }
            ProofTactic::Cases(proof_cases) => {
                let blocks = tokens.cases_arms(&token_range)?;
                if blocks.len() != proof_cases.arms().len() {
                    return Err(ClickError::new(
                        "source `cases` arms do not match the parsed proof",
                    ));
                }
                for ((open, close), arm) in blocks.into_iter().zip(proof_cases.arms()) {
                    collect_tactic_block_spans(tokens, open, close, arm.tactics(), spans)?;
                }
            }
            ProofTactic::CallOutcomes(outcomes) => {
                let [(returned_open, returned_close), (threw_open, threw_close)] =
                    tokens.labeled_arms(&token_range, ["returned", "threw"])?;
                collect_tactic_block_spans(
                    tokens,
                    returned_open,
                    returned_close,
                    &outcomes.returned_tactics,
                    spans,
                )?;
                collect_tactic_block_spans(
                    tokens,
                    threw_open,
                    threw_close,
                    &outcomes.threw_tactics,
                    spans,
                )?;
            }
            ProofTactic::Match(proof_match) => {
                let arms = &proof_match.arms;
                let arm_blocks = tokens.child_blocks(&token_range);
                if arm_blocks.len() != arms.len() {
                    return Err(ClickError::new(format!(
                        "source proof match has {} arm(s), but the parsed tactic has {}",
                        arm_blocks.len(),
                        arms.len()
                    )));
                }
                for (arm, (arm_open, arm_close)) in arms.iter().zip(arm_blocks) {
                    collect_tactic_block_spans(tokens, arm_open, arm_close, &arm.tactics, spans)?;
                }
            }
            ProofTactic::Loop(clause) => {
                for (phase, proof) in [
                    ("initialize", clause.initialize_proof()),
                    ("maintain", clause.preserve_proof()),
                ] {
                    if let Some(proof) = proof {
                        let (_, phase_clause) =
                            tokens.loop_phase(&token_range, phase).ok_or_else(|| {
                                ClickError::new(format!(
                                    "parsed frontier-local loop has `{phase}` proof but source block does not"
                                ))
                            })?;
                        collect_nested_proof_spans(tokens, phase_clause, proof, spans)?;
                    }
                }
                if let Some(body) = clause.otherwise_proof().and_then(SourceProof::tactics) {
                    let (_, phase) =
                        tokens
                            .loop_phase(&token_range, "otherwise")
                            .ok_or_else(|| {
                                ClickError::new(
                                    "parsed loop has an otherwise block with no source span",
                                )
                            })?;
                    collect_tactic_block_spans(tokens, phase.start, phase.last, body, spans)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn collect_nested_proof_spans<'t>(
    tokens: &ProofTokens<'_>,
    clause: parsed_blocks::ProofClause,
    proof: &'t SourceProof,
    spans: &mut Vec<FlatSourceTactic<'t>>,
) -> Result<(), ClickError> {
    // A loop phase's `by` opens its block, written or implicit.
    let by = clause.start;
    let open = by + 1;
    match proof {
        SourceProof::Default => Ok(()),
        SourceProof::Tactic(smart) => {
            let first = open + 1;
            let last = tokens.block_close(open)? - 1;
            spans.push(FlatSourceTactic {
                span: tokens[first].span.start..tokens[last].span.end,
                tokens: first..last + 1,
                tactic: FlatTactic::Phase(*smart, by),
            });
            Ok(())
        }
        SourceProof::Script(tactics) => {
            let close = tokens.block_close(open)?;
            collect_tactic_block_spans(tokens, open, close, tactics, spans)
        }
    }
}

#[cfg(test)]
fn find_tactic_span(
    tokens: &ProofTokens<'_>,
    proof_span: &Range<usize>,
    wanted: usize,
) -> Result<Range<usize>, ClickError> {
    let by = tokens
        .binary_search_by_key(&proof_span.start, |token| token.span.start)
        .ok()
        .filter(|index| tokens[*index].text == "by")
        .ok_or_else(|| ClickError::new("could not locate selected source proof"))?;
    let open = by + 1;
    if tokens.get(open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new(
            "individual tactic expansion requires an explicit `by { ... }` proof",
        ));
    }
    let close = tokens.block_close(open)?;
    if let Some(range) = tokens.tactic_ranges(open, close)?.get(wanted) {
        return Ok(tokens[range.start].span.start..tokens[range.end - 1].span.end);
    }
    Err(ClickError::new(format!(
        "selected source proof has no tactic {wanted}"
    )))
}

/// The steps of a written script's implicit tail, on the lines after the
/// script's last written tactic; nothing when the tail had nothing to do.
fn appended_tail(tactics: &[ProofTactic]) -> String {
    if tactics.is_empty() {
        return String::new();
    }
    format!(
        "\n{}",
        super::printing::format_partial_tactic_sequence(tactics)
    )
}

fn indent_replacement(source: &str, start: usize, replacement: &str) -> String {
    let line_start = source[..start].rfind('\n').map_or(0, |index| index + 1);
    let line_prefix = &source[line_start..start];
    let indent_length = line_prefix.len() - line_prefix.trim_start().len();
    let indent = &line_prefix[..indent_length];
    replacement.replace('\n', &format!("\n{indent}"))
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod loop_entry_capture_scaling_tests {
    use super::*;
    include!("../scaling_tests/surface/expansion/loop_entry_captures.rs");
}

thread_local! {
    static TERMINATION_CERTIFICATE: std::cell::RefCell<Option<Option<ProofCertificate>>> = const { std::cell::RefCell::new(None) };
}

pub(in crate::surface) fn record_termination_certificate(certificate: &ProofCertificate) {
    TERMINATION_CERTIFICATE.with(|slot| {
        if let Some(output) = slot.borrow_mut().as_mut() {
            *output = Some(certificate.clone());
        }
    });
}

fn capture_termination_certificate<T>(
    operation: impl FnOnce() -> T,
) -> (T, Option<ProofCertificate>) {
    struct Restore(Option<Option<ProofCertificate>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            TERMINATION_CERTIFICATE.with(|slot| *slot.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(TERMINATION_CERTIFICATE.with(|slot| slot.replace(Some(None))));
    let result = operation();
    let certificate =
        TERMINATION_CERTIFICATE.with(|slot| slot.borrow_mut().as_mut().and_then(Option::take));
    (result, certificate)
}
