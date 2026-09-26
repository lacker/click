use std::ops::Range;

use super::validation::tactic_name;
use super::*;
use crate::languages::c::target::CTarget;
use crate::languages::c::thread_runtime::CThreadRuntime;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CProofClaim {
    Ensure(usize),
    ExceptionalEnsure(usize),
    Grouped,
}

pub fn verifying_source_paths(click_source: &str) -> Result<Vec<String>, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
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

/// Rewrites the path literal of every `verifying "..."` declaration whose
/// current spelling selects a rebased file, keeping all other source text
/// byte-identical. Callers supply the mapping: `None` keeps a declaration
/// unchanged, and the caller guarantees the mapped spelling resolves to the
/// same source from its own loading rules.
pub fn map_verifying_source_paths(
    click_source: &str,
    map: impl Fn(&str) -> Option<String>,
) -> Result<String, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let mut replacements = Vec::new();
    for window in tokens.windows(2) {
        if window[0].text == "verifying"
            && window[1].text.starts_with('"')
            && window[1].text.ends_with('"')
        {
            let declared = &window[1].text[1..window[1].text.len() - 1];
            let Some(rebased) = map(declared) else {
                continue;
            };
            if rebased.contains('\\') || rebased.contains('"') {
                return Err(ClickError::new(format!(
                    "rebased verifying declaration `{rebased}` is not a supported path literal"
                )));
            }
            replacements.push((window[1].span.clone(), format!("\"{rebased}\"")));
        }
    }
    let mut rebased = String::with_capacity(click_source.len());
    let mut cursor = 0;
    for (Range { start, end }, spelled) in replacements {
        rebased.push_str(&click_source[cursor..start]);
        rebased.push_str(&spelled);
        cursor = end;
    }
    rebased.push_str(&click_source[cursor..]);
    Ok(rebased)
}

/// Finds the top-level `target "..."` directive that selects the C
/// implementation target, before any C source is preprocessed. Include
/// expansion needs the target, and expansion happens before the sidecar is
/// parsed, so this scan and the parser share one accepted-name registry.
/// Absent directive selects the default target.
pub fn selected_c_target(click_source: &str) -> Result<CTarget, ClickError> {
    Ok(declared_c_target(click_source)?.unwrap_or(CTarget::SUPPORTED))
}

/// Scans the explicit runtime selector before the full sidecar is parsed.
/// Incremental sessions use it to refuse a changed runtime identity.
pub fn selected_thread_runtime(click_source: &str) -> Result<CThreadRuntime, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
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
    let tokens = scan_source_tokens(click_source)?;
    let mut selected = None;
    let mut depth = 0usize;
    for window in tokens.windows(3) {
        // The directive is a file item, so only brace depth zero can hold one.
        // A deeper `target "..."` spelling is not a directive here and must
        // not be one for the parser either.
        match window[0].text.as_str() {
            "{" => depth += 1,
            "}" => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth > 0
            || window[0].text != "target"
            || !window[1].text.starts_with('"')
            || !window[1].text.ends_with('"')
            || window[1].text.len() < 2
            || window[2].text != ";"
        {
            continue;
        }
        let name = &window[1].text[1..window[1].text.len() - 1];
        let target = CTarget::from_name(name).ok_or_else(|| {
            ClickError::new(format!(
                "unknown C target `{name}`; accepted targets are {}",
                CTarget::accepted_names()
            ))
        })?;
        if selected.is_some() {
            return Err(ClickError::new(
                "a Click file declares more than one `target`".to_string(),
            ));
        }
        selected = Some(target);
    }
    Ok(selected)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickImportSite {
    pub path: String,
    pub position: SourcePosition,
}

/// Finds top-level import declarations for the filesystem graph loader. Full
/// syntax and interface validation still happens in the shared parser.
pub fn click_import_sites(click_source: &str) -> Result<Vec<ClickImportSite>, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
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
pub fn expand_c0_claim_source(
    click_source: &str,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    let function_block = file
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let grouped = function_block.grouped_proof().is_some();
    let edit = if grouped || claim == CProofClaim::Grouped {
        ProofSourceEdit::Explicit(find_grouped_proof_span(&tokens, &function)?)
    } else {
        find_claim_proof_edit(&tokens, &function, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = verify_c0_sources_at(click_source, c_sources, target.line, target.column)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = checked_claim_expansion_source(
        theorem,
        function_block.grouped_proof().is_some() || claim == CProofClaim::Grouped,
    )?;
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
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    Ok(expanded)
}

fn expand_c0_project_claim_source(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let sources = CSourceContext::bundle(c_sources).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let function_block = file
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let edit = if function_block.grouped_proof().is_some() || claim == CProofClaim::Grouped {
        ProofSourceEdit::Explicit(find_grouped_proof_span(&tokens, &function)?)
    } else {
        find_claim_proof_edit(&tokens, &function, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = verify_c0_project_at(project, c_sources, target.line, target.column)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = checked_claim_expansion_source(
        theorem,
        function_block.grouped_proof().is_some() || claim == CProofClaim::Grouped,
    )?;
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
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    Ok(expanded)
}

fn expand_c0_prepared_project_claim_source(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let sources = CSourceContext::prepared(imports).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let function_block = file
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let edit = if function_block.grouped_proof().is_some() || claim == CProofClaim::Grouped {
        ProofSourceEdit::Explicit(find_grouped_proof_span(&tokens, &function)?)
    } else {
        find_claim_proof_edit(&tokens, &function, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = verify_c0_prepared_project_at(project, imports, target.line, target.column)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = checked_claim_expansion_source(
        theorem,
        function_block.grouped_proof().is_some() || claim == CProofClaim::Grouped,
    )?;
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
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    Ok(expanded)
}

fn expand_c0_prepared_claim_source(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError> {
    let sources = CSourceContext::prepared(imports);
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let file = parse_source_with_c_layouts_context(click_source, &sources)?;
    let function_block = file
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let grouped = function_block.grouped_proof().is_some();
    let edit = if grouped || claim == CProofClaim::Grouped {
        ProofSourceEdit::Explicit(find_grouped_proof_span(&tokens, &function)?)
    } else {
        find_claim_proof_edit(&tokens, &function, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified =
        verify_c0_prepared_sources_at(click_source, imports, target.line, target.column)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = checked_claim_expansion_source(
        theorem,
        function_block.grouped_proof().is_some() || claim == CProofClaim::Grouped,
    )?;
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
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    Ok(expanded)
}

/// Expands one function claim selected by the same stable label used by
/// profiling and diagnostics.
pub fn expand_c0_claim_source_by_label(
    click_source: &str,
    c_sources: &[(&str, &str)],
    claim_label: &str,
) -> Result<String, ClickError> {
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    for theorem in file.theorem_definitions() {
        for (index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            if label == claim_label {
                return expand_pure_theorem_source(click_source, c_sources, theorem.name(), index);
            }
        }
    }
    for function in file.function_blocks() {
        let function_name = function.signature().name();
        if claim_label == format!("{function_name}.contract") && function.grouped_proof().is_some()
        {
            return expand_c0_claim_source(
                click_source,
                c_sources,
                function_name,
                CProofClaim::Grouped,
            );
        }
        for (index, ensure) in function.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{function_name}.ensures_{index}"),
                |name| format!("{function_name}.{name}"),
            );
            if label == claim_label {
                return expand_c0_claim_source(
                    click_source,
                    c_sources,
                    function_name,
                    CProofClaim::Ensure(index),
                );
            }
        }
    }
    Err(ClickError::new(format!(
        "could not locate function claim `{claim_label}`"
    )))
}

pub fn expand_c0_project_claim_source_by_label(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    claim_label: &str,
) -> Result<String, ClickError> {
    project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let sources = CSourceContext::bundle(c_sources).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        for (index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            if label == claim_label {
                return expand_project_pure_theorem_source(
                    project,
                    c_sources,
                    theorem.name(),
                    index,
                );
            }
        }
    }
    for function in file.function_blocks() {
        let function_name = function.signature().name();
        if claim_label == format!("{function_name}.contract") && function.grouped_proof().is_some()
        {
            return expand_c0_project_claim_source(
                project,
                c_sources,
                function_name,
                CProofClaim::Grouped,
            );
        }
        for (index, ensure) in function.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{function_name}.ensures_{index}"),
                |name| format!("{function_name}.{name}"),
            );
            if label == claim_label {
                return expand_c0_project_claim_source(
                    project,
                    c_sources,
                    function_name,
                    CProofClaim::Ensure(index),
                );
            }
        }
    }
    Err(ClickError::new(format!(
        "could not locate function claim `{claim_label}`"
    )))
}

pub fn expand_c0_prepared_claim_source_by_label(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    claim_label: &str,
) -> Result<String, ClickError> {
    let sources = CSourceContext::prepared(imports);
    let file = parse_source_with_c_layouts_context(click_source, &sources)?;
    for theorem in file.theorem_definitions() {
        for (index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            if label == claim_label {
                return expand_pure_theorem_source_context(
                    click_source,
                    &sources,
                    theorem.name(),
                    index,
                );
            }
        }
    }
    for function in file.function_blocks() {
        let function_name = function.signature().name();
        if claim_label == format!("{function_name}.contract") && function.grouped_proof().is_some()
        {
            return expand_c0_prepared_claim_source(
                click_source,
                imports,
                function_name,
                CProofClaim::Grouped,
            );
        }
        for (index, ensure) in function.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{function_name}.ensures_{index}"),
                |name| format!("{function_name}.{name}"),
            );
            if label == claim_label {
                return expand_c0_prepared_claim_source(
                    click_source,
                    imports,
                    function_name,
                    CProofClaim::Ensure(index),
                );
            }
        }
    }
    Err(ClickError::new(format!(
        "could not locate function claim `{claim_label}`"
    )))
}

pub fn expand_c0_prepared_project_claim_source_by_label(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    claim_label: &str,
) -> Result<String, ClickError> {
    let sources = CSourceContext::prepared(imports).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        for (index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            if label == claim_label {
                return expand_prepared_project_pure_theorem_source(
                    project,
                    imports,
                    theorem.name(),
                    index,
                );
            }
        }
    }
    for function in file.function_blocks() {
        let function_name = function.signature().name();
        if claim_label == format!("{function_name}.contract") && function.grouped_proof().is_some()
        {
            return expand_c0_prepared_project_claim_source(
                project,
                imports,
                function_name,
                CProofClaim::Grouped,
            );
        }
        for (index, ensure) in function.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{function_name}.ensures_{index}"),
                |name| format!("{function_name}.{name}"),
            );
            if label == claim_label {
                return expand_c0_prepared_project_claim_source(
                    project,
                    imports,
                    function_name,
                    CProofClaim::Ensure(index),
                );
            }
        }
    }
    Err(ClickError::new(format!(
        "could not locate function claim `{claim_label}`"
    )))
}

pub fn expand_cpp_prepared_claim_source_by_label(
    click_source: &str,
    import: &crate::languages::cpp::PreparedCppImport,
    claim_label: &str,
) -> Result<String, ClickError> {
    expand_cpp_prepared_claim_source_by_label_context(None, click_source, import, claim_label)
}

pub fn expand_cpp_prepared_project_claim_source_by_label(
    project: &ClickProject,
    import: &crate::languages::cpp::PreparedCppImport,
    claim_label: &str,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    expand_cpp_prepared_claim_source_by_label_context(
        Some(project),
        click_source,
        import,
        claim_label,
    )
}

fn expand_cpp_prepared_claim_source_by_label_context(
    project: Option<&ClickProject>,
    click_source: &str,
    import: &crate::languages::cpp::PreparedCppImport,
    claim_label: &str,
) -> Result<String, ClickError> {
    let sources = match project {
        Some(project) => CSourceContext::cpp(import)?.with_click_project(project),
        None => CSourceContext::cpp(import)?,
    };
    let file = match project {
        Some(project) => resolve_click_project_context(project, &sources)?,
        None => parse_source_with_c_layouts_context(click_source, &sources)?,
    };
    for function in file.function_blocks() {
        let function_name = function.signature().name();
        if claim_label == format!("{function_name}.contract") && function.grouped_proof().is_some()
        {
            return expand_cpp_prepared_claim_source_context(
                project,
                click_source,
                import,
                function_name,
                CProofClaim::Grouped,
            );
        }
        for (index, ensure) in function.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{function_name}.ensures_{index}"),
                |name| format!("{function_name}.{name}"),
            );
            if label == claim_label {
                return expand_cpp_prepared_claim_source_context(
                    project,
                    click_source,
                    import,
                    function_name,
                    CProofClaim::Ensure(index),
                );
            }
        }
        for (index, ensure) in function.exceptional_ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{function_name}.exceptional_ensures_{index}"),
                |name| format!("{function_name}.{name}"),
            );
            if label == claim_label {
                return expand_cpp_prepared_claim_source_context(
                    project,
                    click_source,
                    import,
                    function_name,
                    CProofClaim::ExceptionalEnsure(index),
                );
            }
        }
    }
    Err(ClickError::new(format!(
        "could not locate C++ function claim `{claim_label}`"
    )))
}

fn expand_cpp_prepared_claim_source_context(
    project: Option<&ClickProject>,
    click_source: &str,
    import: &crate::languages::cpp::PreparedCppImport,
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError> {
    let sources = match project {
        Some(project) => CSourceContext::cpp(import)?.with_click_project(project),
        None => CSourceContext::cpp(import)?,
    };
    let file = match project {
        Some(project) => resolve_click_project_context(project, &sources)?,
        None => parse_source_with_c_layouts_context(click_source, &sources)?,
    };
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let function_block = file
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let edit = if function_block.grouped_proof().is_some() || claim == CProofClaim::Grouped {
        ProofSourceEdit::Explicit(find_grouped_proof_span(&tokens, &function)?)
    } else {
        find_claim_proof_edit(&tokens, &function, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = match project {
        Some(project) => {
            verify_cpp_prepared_project_at(project, import, target.line, target.column)?
        }
        None => verify_cpp_prepared_sources_at(click_source, import, target.line, target.column)?,
    };
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = checked_claim_expansion_source(
        theorem,
        function_block.grouped_proof().is_some() || claim == CProofClaim::Grouped,
    )?;
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
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    Ok(expanded)
}

pub use crate::source::SourcePosition;

/// One source-selectable smart tactic in a parsed `.click` sidecar.
///
/// This inventory is purely syntactic: producing it does not execute or verify
/// any proof. `source_index` uses the same pre-order indexing as tactic timing
/// and individual source expansion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmartTacticSourceSite {
    pub claim_label: String,
    pub source_index: usize,
    pub tactic_name: String,
}

/// Inventories every source-selectable smart tactic without running proofs.
pub fn c0_smart_tactic_source_sites(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    c0_smart_tactic_source_sites_context(click_source, &sources)
}

pub fn c0_prepared_smart_tactic_source_sites(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::prepared(imports);
    c0_smart_tactic_source_sites_context(click_source, &sources)
}

pub fn cpp_prepared_smart_tactic_source_sites(
    click_source: &str,
    import: &crate::languages::cpp::PreparedCppImport,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::cpp(import)?;
    c0_smart_tactic_source_sites_context(click_source, &sources)
}

pub fn c0_project_smart_tactic_source_sites(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::bundle(c_sources).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_smart_tactic_source_sites_file(&file)
}

pub fn c0_prepared_project_smart_tactic_source_sites(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::prepared(imports).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_smart_tactic_source_sites_file(&file)
}

pub fn cpp_prepared_project_smart_tactic_source_sites(
    project: &ClickProject,
    import: &crate::languages::cpp::PreparedCppImport,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::cpp(import)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_smart_tactic_source_sites_file(&file)
}

fn c0_smart_tactic_source_sites_context(
    click_source: &str,
    sources: &CSourceContext<'_>,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let file = parse_source_with_c_layouts_context(click_source, sources)?;
    c0_smart_tactic_source_sites_file(&file)
}

fn c0_smart_tactic_source_sites_file(
    file: &ClickFile,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let mut sites = Vec::new();
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        // These declarations are checked against kernel axioms, not expanded
        // by an implicit auto tactic. Keep genuine callback refinement proofs
        // (which run before the arithmetic-axiom branch) in the inventory.
        let kernel_axiom_name = proof::is_kernel_standard_theorem_name(theorem.name())
            && theorem
                .parameters()
                .iter()
                .all(|parameter| parameter.click_type() == &ClickType::C(C0Type::Int32));
        for (ensure_index, ensure) in theorem.ensures().iter().enumerate() {
            if kernel_axiom_name
                && !matches!(
                    ensure.ensure(),
                    Ensure::Proposition(ClickProposition::PredicateCall { .. })
                )
            {
                continue;
            }
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{ensure_index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            collect_smart_proof_sites(&label, ensure.proof(), &mut sites);
        }
    }
    for function in file.function_blocks() {
        let function_name = function.signature().name();
        for clause in function.structural_clauses() {
            if let CodeRegion::Loop(loop_index) = clause.region() {
                let default = SourceProof::Default;
                collect_smart_proof_sites(
                    &format!("{function_name}.loop({loop_index}).initialize"),
                    clause.initialize_proof().unwrap_or(&default),
                    &mut sites,
                );
                collect_smart_proof_sites(
                    &format!("{function_name}.loop({loop_index}).preserve"),
                    clause.preserve_proof().unwrap_or(&default),
                    &mut sites,
                );
            }
        }
        if let Some(proof) = function.grouped_proof() {
            collect_smart_proof_sites(&format!("{function_name}.contract"), proof, &mut sites);
            continue;
        }
        for (index, ensure) in function.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{function_name}.ensures_{index}"),
                |name| format!("{function_name}.{name}"),
            );
            collect_smart_proof_sites(&label, ensure.proof(), &mut sites);
        }
    }
    Ok(sites)
}

fn collect_smart_proof_sites(
    claim_label: &str,
    proof: &SourceProof,
    sites: &mut Vec<SmartTacticSourceSite>,
) {
    match proof {
        SourceProof::Default => sites.push(SmartTacticSourceSite {
            claim_label: claim_label.to_string(),
            source_index: 0,
            tactic_name: "auto".to_string(),
        }),
        SourceProof::Tactic(tactic) => sites.push(SmartTacticSourceSite {
            claim_label: claim_label.to_string(),
            source_index: 0,
            tactic_name: match tactic {
                SmartTactic::Auto => "auto",
                SmartTactic::Simp => "simp",
            }
            .to_string(),
        }),
        SourceProof::Script(tactics) => {
            collect_smart_script_sites(claim_label, tactics, 0, sites);
        }
    }
}

fn collect_smart_script_sites(
    claim_label: &str,
    tactics: &[ProofTactic],
    source_index_offset: usize,
    sites: &mut Vec<SmartTacticSourceSite>,
) {
    let mut source_index = source_index_offset;
    for tactic in tactics {
        if source_site_kind(tactic) == SourceSiteKind::ExpandableAutomation {
            sites.push(SmartTacticSourceSite {
                claim_label: claim_label.to_string(),
                source_index,
                tactic_name: tactic_name(tactic).to_string(),
            });
        }
        match tactic {
            ProofTactic::Open(open) => {
                collect_smart_script_sites(claim_label, &open.tactics, source_index + 1, sites);
            }
            ProofTactic::If(proof_if) => {
                collect_smart_script_sites(
                    claim_label,
                    &proof_if.then_tactics,
                    source_index + 1,
                    sites,
                );
                collect_smart_script_sites(
                    claim_label,
                    &proof_if.else_tactics,
                    source_index + 1 + source_tactic_count(&proof_if.then_tactics),
                    sites,
                );
            }
            ProofTactic::StructuralInduct { arms, .. } => {
                let mut nested_source_index = source_index + 1;
                for arm in arms {
                    collect_smart_script_sites(
                        claim_label,
                        &arm.tactics,
                        nested_source_index,
                        sites,
                    );
                    nested_source_index += source_tactic_count(&arm.tactics);
                }
            }
            ProofTactic::Match(proof_match) => {
                let arms = &proof_match.arms;
                let mut nested_source_index = source_index + 1;
                for arm in arms {
                    collect_smart_script_sites(
                        claim_label,
                        &arm.tactics,
                        nested_source_index,
                        sites,
                    );
                    nested_source_index += source_tactic_count(&arm.tactics);
                }
            }
            ProofTactic::Branch(proof_branch) => {
                collect_smart_script_sites(
                    claim_label,
                    &proof_branch.then_tactics,
                    source_index + 1,
                    sites,
                );
                collect_smart_script_sites(
                    claim_label,
                    &proof_branch.else_tactics,
                    source_index + 1 + source_tactic_count(&proof_branch.then_tactics),
                    sites,
                );
            }
            ProofTactic::Loop(clause) => {
                let mut nested_source_index = source_index + 1;
                if let Some(proof) = clause.initialize_proof() {
                    collect_smart_nested_proof_sites(
                        claim_label,
                        proof,
                        nested_source_index,
                        sites,
                    );
                    nested_source_index += proof_source_tactic_count(proof);
                }
                if let Some(proof) = clause.preserve_proof() {
                    collect_smart_nested_proof_sites(
                        claim_label,
                        proof,
                        nested_source_index,
                        sites,
                    );
                }
            }
            _ => {}
        }
        source_index += source_tactic_count(std::slice::from_ref(tactic));
    }
}

fn collect_smart_nested_proof_sites(
    claim_label: &str,
    proof: &SourceProof,
    source_index: usize,
    sites: &mut Vec<SmartTacticSourceSite>,
) {
    match proof {
        SourceProof::Default => {}
        SourceProof::Tactic(tactic) => sites.push(SmartTacticSourceSite {
            claim_label: claim_label.to_string(),
            source_index,
            tactic_name: match tactic {
                SmartTactic::Auto => "auto",
                SmartTactic::Simp => "simp",
            }
            .to_string(),
        }),
        SourceProof::Script(tactics) => {
            collect_smart_script_sites(claim_label, tactics, source_index, sites)
        }
    }
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
    let sources = CSourceContext::bundle(c_sources);
    verification_target_at_context(click_source, &sources, line, column)
}

pub(super) fn verification_target_at_context(
    click_source: &str,
    c_sources: &CSourceContext<'_>,
    line: usize,
    column: usize,
) -> Result<VerificationTarget, ClickError> {
    let file = parse_source_with_c_layouts_context(click_source, c_sources)?;
    verification_target_at_file(click_source, &file, line, column)
}

pub(in crate::surface) fn verification_target_at_file(
    click_source: &str,
    file: &ClickFile,
    line: usize,
    column: usize,
) -> Result<VerificationTarget, ClickError> {
    let wanted = offset_at_position(click_source, line, column)?;
    let tokens = scan_source_tokens(click_source)?;
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        let source = find_theorem(&tokens, theorem.name())?;
        if tokens[source.body_open].span.start <= wanted
            && wanted <= tokens[source.body_close].span.end
        {
            return Ok(VerificationTarget::Theorem(theorem.name().to_string()));
        }
    }
    for function in file.function_blocks() {
        let function_name = function.signature().name();
        let source = find_function(&tokens, function_name)?;
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
const UNSPELLABLE_POINTER_FORMS: [&str; 5] = [
    "symbolic-pointer:",
    "symbolic-function-pointer:",
    "heap-allocation:",
    "arg-memory",
    "string:",
];

/// Reports why a rendered expansion is not Click. A composite resource's
/// existential witness is bound to a kernel pointer with no source spelling
/// (the language reference states that a witness needs no syntax at fold or
/// unfold), so a certificate that has to cite the witness cannot be written
/// at all. Naming the witness reports the language gap; the parse error does
/// not.
fn unparseable_expansion_error(
    click_source: &str,
    sources: &CSourceContext<'_>,
    replacement: &str,
    parse_error: ClickError,
) -> ClickError {
    let file = parse_source_with_c_layouts_context(click_source, sources).ok();
    unparseable_expansion_error_for_file(replacement, parse_error, file.as_ref())
}

fn unparseable_expansion_error_for_file(
    replacement: &str,
    parse_error: ClickError,
    file: Option<&ClickFile>,
) -> ClickError {
    if !UNSPELLABLE_POINTER_FORMS
        .iter()
        .any(|form| replacement.contains(form))
    {
        return ClickError::new(format!(
            "the expansion did not parse as Click: {}",
            parse_error.message()
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
        "the expansion needs a name for {named}, which has no surface spelling"
    ))
}

/// Rejects a rendered expansion that is not Click before it reaches the
/// caller's verification, so the reported failure is the missing name rather
/// than the parse error the unparseable text produces.
fn checked_expanded_source(
    click_source: &str,
    sources: &CSourceContext<'_>,
    replacement: &str,
    expanded: String,
) -> Result<String, ClickError> {
    match parse_source_with_c_layouts_context(&expanded, sources) {
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
pub fn expand_c0_tactic_source_at(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    expand_c0_tactic_source_at_context(None, click_source, c_sources, line, column)
}

pub fn expand_c0_project_tactic_source_at(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    expand_c0_tactic_source_at_context(Some(project), click_source, c_sources, line, column)
}

fn expand_c0_tactic_source_at_context(
    project: Option<&ClickProject>,
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let selected = if let Some(project) = project {
        let sources = CSourceContext::bundle(c_sources).with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        locate_source_tactic_file(click_source, &file, line, column)?
    } else {
        locate_source_tactic(click_source, c_sources, line, column)?
    };
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &selected.site
    {
        return if let Some(project) = project {
            expand_project_pure_theorem_source(project, c_sources, theorem_name, *ensure_index)
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
            expand_c0_project_claim_source(project, c_sources, function_name, *claim)
        } else {
            expand_c0_claim_source(click_source, c_sources, function_name, *claim)
        };
    }
    let replacement_tactics = match &selected.edit {
        TacticSourceEdit::Partial(_) | TacticSourceEdit::PartialProofClause(_) => {
            if let Some(project) = project {
                super::proof::capture_c0_project_tactic_expansion(
                    project,
                    c_sources,
                    selected.site.clone(),
                    selected.source_index,
                )?
            } else {
                super::proof::capture_c0_tactic_expansion(
                    click_source,
                    c_sources,
                    selected.site.clone(),
                    selected.source_index,
                )?
            }
        }
        TacticSourceEdit::WholeProof(_) => {
            if let Some(project) = project {
                super::proof::capture_c0_project_proof_site_expansion(
                    project,
                    c_sources,
                    selected.site.clone(),
                )?
            } else {
                super::proof::capture_c0_proof_site_expansion(
                    click_source,
                    c_sources,
                    selected.site.clone(),
                )?
            }
        }
    };
    let (span, replacement) = match selected.edit {
        TacticSourceEdit::Partial(span) => (
            span,
            super::printing::format_partial_tactic_sequence(&replacement_tactics),
        ),
        TacticSourceEdit::PartialProofClause(span) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: {error:?}"
                    ))
                })?;
            (
                span,
                super::printing::format_proof_certificate(&certificate),
            )
        }
        TacticSourceEdit::WholeProof(edit) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: {error:?}"
                    ))
                })?;
            let replacement = super::printing::format_proof_certificate(&certificate);
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
                    let replacement = replacement.replace('\n', "\n    ");
                    format!("    {phase} {replacement}\n")
                }
            };
            (span, replacement)
        }
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
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    if let Some(project) = project {
        let rewritten = project.with_entry_source(expanded.clone());
        let sources = CSourceContext::bundle(c_sources).with_click_project(&rewritten);
        match resolve_click_project_context(&rewritten, &sources) {
            Ok(_) => Ok(expanded),
            Err(error) => {
                let original_sources =
                    CSourceContext::bundle(c_sources).with_click_project(project);
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
            &CSourceContext::bundle(c_sources),
            &replacement,
            expanded,
        )
    }
}

/// Expands one tactic using compiler-prepared translation units throughout
/// location, capture, and certificate verification.
pub fn expand_c0_prepared_tactic_source_at(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    expand_c0_prepared_tactic_source_at_context(None, click_source, imports, line, column)
}

pub fn expand_c0_prepared_project_tactic_source_at(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    expand_c0_prepared_tactic_source_at_context(Some(project), click_source, imports, line, column)
}

pub fn expand_cpp_prepared_tactic_source_at(
    click_source: &str,
    import: &crate::languages::cpp::PreparedCppImport,
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    expand_cpp_prepared_tactic_source_at_context(None, click_source, import, line, column)
}

pub fn expand_cpp_prepared_project_tactic_source_at(
    project: &ClickProject,
    import: &crate::languages::cpp::PreparedCppImport,
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    expand_cpp_prepared_tactic_source_at_context(Some(project), click_source, import, line, column)
}

fn expand_cpp_prepared_tactic_source_at_context(
    project: Option<&ClickProject>,
    click_source: &str,
    import: &crate::languages::cpp::PreparedCppImport,
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let sources = match project {
        Some(project) => CSourceContext::cpp(import)?.with_click_project(project),
        None => CSourceContext::cpp(import)?,
    };
    let file = match project {
        Some(project) => resolve_click_project_context(project, &sources)?,
        None => parse_source_with_c_layouts_context(click_source, &sources)?,
    };
    let selected = locate_source_tactic_file(click_source, &file, line, column)?;
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &selected.site
    {
        let verified = match project {
            Some(project) => verify_click_project_theorem_context(project, &sources, theorem_name)?,
            None => verify_click_theorems_with_context(click_source, &sources)?,
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
        return expand_cpp_prepared_claim_source_context(
            project,
            click_source,
            import,
            function_name,
            *claim,
        );
    }
    let replacement_tactics = match &selected.edit {
        TacticSourceEdit::Partial(_) | TacticSourceEdit::PartialProofClause(_) => {
            if let Some(project) = project {
                super::proof::capture_cpp_prepared_project_tactic_expansion(
                    project,
                    import,
                    selected.site.clone(),
                    selected.source_index,
                )?
            } else {
                super::proof::capture_cpp_prepared_tactic_expansion(
                    click_source,
                    import,
                    selected.site.clone(),
                    selected.source_index,
                )?
            }
        }
        TacticSourceEdit::WholeProof(_) => {
            if let Some(project) = project {
                super::proof::capture_cpp_prepared_project_proof_site_expansion(
                    project,
                    import,
                    selected.site.clone(),
                )?
            } else {
                super::proof::capture_cpp_prepared_proof_site_expansion(
                    click_source,
                    import,
                    selected.site.clone(),
                )?
            }
        }
    };
    let (span, replacement) = match selected.edit {
        TacticSourceEdit::Partial(span) => (
            span,
            super::printing::format_partial_tactic_sequence(&replacement_tactics),
        ),
        TacticSourceEdit::PartialProofClause(span) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: {error:?}"
                    ))
                })?;
            (
                span,
                super::printing::format_proof_certificate(&certificate),
            )
        }
        TacticSourceEdit::WholeProof(edit) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: {error:?}"
                    ))
                })?;
            let replacement = super::printing::format_proof_certificate(&certificate);
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
    };
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    checked_expanded_source(click_source, &sources, &replacement, expanded)
}

fn expand_c0_prepared_tactic_source_at_context(
    project: Option<&ClickProject>,
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let sources = CSourceContext::prepared(imports);
    let selected = if let Some(project) = project {
        let project_sources = CSourceContext::prepared(imports).with_click_project(project);
        let file = resolve_click_project_context(project, &project_sources)?;
        locate_source_tactic_file(click_source, &file, line, column)?
    } else {
        locate_source_tactic_context(click_source, &sources, line, column)?
    };
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &selected.site
    {
        return if let Some(project) = project {
            expand_prepared_project_pure_theorem_source(
                project,
                imports,
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
            expand_c0_prepared_project_claim_source(project, imports, function_name, *claim)
        } else {
            expand_c0_prepared_claim_source(click_source, imports, function_name, *claim)
        };
    }
    let replacement_tactics = match &selected.edit {
        TacticSourceEdit::Partial(_) | TacticSourceEdit::PartialProofClause(_) => {
            if let Some(project) = project {
                super::proof::capture_c0_prepared_project_tactic_expansion(
                    project,
                    imports,
                    selected.site.clone(),
                    selected.source_index,
                )?
            } else {
                super::proof::capture_c0_prepared_tactic_expansion(
                    click_source,
                    imports,
                    selected.site.clone(),
                    selected.source_index,
                )?
            }
        }
        TacticSourceEdit::WholeProof(_) => {
            if let Some(project) = project {
                super::proof::capture_c0_prepared_project_proof_site_expansion(
                    project,
                    imports,
                    selected.site.clone(),
                )?
            } else {
                super::proof::capture_c0_prepared_proof_site_expansion(
                    click_source,
                    imports,
                    selected.site.clone(),
                )?
            }
        }
    };
    let (span, replacement) = match selected.edit {
        TacticSourceEdit::Partial(span) => (
            span,
            super::printing::format_partial_tactic_sequence(&replacement_tactics),
        ),
        TacticSourceEdit::PartialProofClause(span) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: {error:?}"
                    ))
                })?;
            (
                span,
                super::printing::format_proof_certificate(&certificate),
            )
        }
        TacticSourceEdit::WholeProof(edit) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: {error:?}"
                    ))
                })?;
            let replacement = super::printing::format_proof_certificate(&certificate);
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
    };
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    if let Some(project) = project {
        let rewritten = project.with_entry_source(expanded.clone());
        let project_sources = CSourceContext::prepared(imports).with_click_project(&rewritten);
        match resolve_click_project_context(&rewritten, &project_sources) {
            Ok(_) => Ok(expanded),
            Err(error) => {
                let original_sources =
                    CSourceContext::prepared(imports).with_click_project(project);
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
    let sources = CSourceContext::bundle(c_sources);
    expand_pure_theorem_source_context(click_source, &sources, theorem_name, ensure_index)
}

fn expand_project_pure_theorem_source(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let verified = verify_click_project_theorem(project, c_sources, theorem_name)?;
    rewrite_verified_pure_theorem(click_source, &verified, theorem_name, ensure_index)
}

fn expand_prepared_project_pure_theorem_source(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let verified = verify_click_prepared_project_theorem(project, imports, theorem_name)?;
    rewrite_verified_pure_theorem(click_source, &verified, theorem_name, ensure_index)
}

fn expand_pure_theorem_source_context(
    click_source: &str,
    sources: &CSourceContext<'_>,
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let verified = verify_click_theorems_with_context(click_source, sources)?;
    rewrite_verified_pure_theorem(click_source, &verified, theorem_name, ensure_index)
}

fn rewrite_verified_pure_theorem(
    click_source: &str,
    verified: &[VerifiedPureTheorem],
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
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
    let replacement = theorem.expanded_proof_source()?;
    let source = find_theorem(&tokens, theorem_name)?;
    let edit = find_ensure_proof_edit(&tokens, source.body_open, source.body_close, ensure_index)?;
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
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    Ok(expanded)
}

/// The explicit proof that replaces a whole claim proof. The rewrite is
/// refused before it is emitted when its regions nest past the bound the
/// checked drivers accept, with the diagnostic verification would give it.
fn checked_claim_expansion_source(
    theorem: &VerifiedCTheorem,
    grouped: bool,
) -> Result<String, ClickError> {
    let certificate = theorem.expanded_proof_certificate()?;
    let function_name = theorem.function_block.signature().name();
    let proof_label = match &theorem.claim {
        _ if grouped => format!("{function_name}.contract"),
        VerifiedClaim::Ensure { index, clause } => match clause.name() {
            Some(name) => format!("{function_name}.{name}"),
            None => format!("{function_name}.ensures_{index}"),
        },
        VerifiedClaim::ExceptionalEnsure { index, clause } => match clause.name() {
            Some(name) => format!("{function_name}.{name}"),
            None => format!("{function_name}.exceptional_ensures_{index}"),
        },
    };
    if let Some(error) = super::proof::proof_region_nesting_bound_error(
        &proof_label,
        &certificate.to_proof_tactics(),
    ) {
        return Err(error);
    }
    Ok(super::printing::format_proof_certificate(&certificate))
}

fn select_expansion_theorem<'a>(
    verified: &'a [VerifiedCTheorem],
    function_name: &str,
    claim: CProofClaim,
) -> Result<&'a VerifiedCTheorem, ClickError> {
    let matches_function =
        |theorem: &&VerifiedCTheorem| theorem.function_block.signature().name() == function_name;
    let selected = match claim {
        CProofClaim::Ensure(index) => verified.iter().find(|theorem| {
            matches_function(theorem)
                && matches!(theorem.claim, VerifiedClaim::Ensure { index: found, .. } if found == index)
        }),
        CProofClaim::ExceptionalEnsure(index) => verified.iter().find(|theorem| {
            matches_function(theorem)
                && matches!(theorem.claim, VerifiedClaim::ExceptionalEnsure { index: found, .. } if found == index)
        }),
        CProofClaim::Grouped => verified
            .iter()
            .find(|theorem| {
                matches_function(theorem)
                    && matches!(theorem.claim, VerifiedClaim::Ensure { .. })
            })
            .or_else(|| verified.iter().find(matches_function)),
    };
    selected.ok_or_else(|| {
        ClickError::new(format!(
            "verified function `{function_name}` has no {claim:?} claim"
        ))
    })
}

#[derive(Clone, Debug)]
struct SourceToken {
    text: String,
    span: Range<usize>,
}

#[derive(Clone, Copy)]
struct FunctionSource {
    body_open: usize,
    body_close: usize,
}

fn scan_source_tokens(source: &str) -> Result<Vec<SourceToken>, ClickError> {
    let mut tokens = Vec::new();
    let mut index = 0;
    while index < source.len() {
        let character = source[index..]
            .chars()
            .next()
            .expect("index is maintained at a character boundary");
        if character.is_whitespace() {
            index += character.len_utf8();
            continue;
        }
        if character == '#' {
            index += source[index..].find('\n').unwrap_or(source.len() - index);
            continue;
        }
        let start = index;
        if character.is_ascii_alphabetic() || character == '_' {
            index += character.len_utf8();
            while index < source.len() {
                let next = source[index..]
                    .chars()
                    .next()
                    .expect("index is maintained at a character boundary");
                if !next.is_ascii_alphanumeric() && next != '_' {
                    break;
                }
                index += next.len_utf8();
            }
        } else if character.is_ascii_digit() {
            index += character.len_utf8();
            while index < source.len() {
                let next = source[index..]
                    .chars()
                    .next()
                    .expect("index is maintained at a character boundary");
                if !next.is_ascii_digit() {
                    break;
                }
                index += next.len_utf8();
            }
        } else if matches!(character, '"' | '\'') {
            let quote = character;
            index += character.len_utf8();
            let mut terminated = false;
            while index < source.len() {
                let next = source[index..]
                    .chars()
                    .next()
                    .expect("index is maintained at a character boundary");
                index += next.len_utf8();
                if next == '\\' {
                    if index < source.len() {
                        let escaped = source[index..]
                            .chars()
                            .next()
                            .expect("index is maintained at a character boundary");
                        index += escaped.len_utf8();
                    }
                } else if next == quote {
                    terminated = true;
                    break;
                }
            }
            if !terminated {
                return Err(ClickError::new(
                    "unterminated literal while locating proof source",
                ));
            }
        } else {
            index += character.len_utf8();
        }
        tokens.push(SourceToken {
            text: source[start..index].to_string(),
            span: start..index,
        });
    }
    Ok(tokens)
}

fn find_function(tokens: &[SourceToken], name: &str) -> Result<FunctionSource, ClickError> {
    for (index, token) in tokens.iter().enumerate() {
        if token.text != name || tokens.get(index + 1).map(|token| token.text.as_str()) != Some("(")
        {
            continue;
        }
        let parameters_close = matching_delimiter(tokens, index + 1, "(", ")")?;
        let mut body_open = parameters_close + 1;
        if tokens.get(body_open).map(|token| token.text.as_str()) == Some("throws") {
            body_open += 2;
        }
        if tokens.get(body_open).map(|token| token.text.as_str()) == Some("diverges") {
            body_open += 1;
        }
        if tokens.get(body_open).map(|token| token.text.as_str()) != Some("{") {
            continue;
        }
        let body_close = matching_delimiter(tokens, body_open, "{", "}")?;
        return Ok(FunctionSource {
            body_open,
            body_close,
        });
    }
    Err(ClickError::new(format!(
        "could not locate Click function block `{name}`"
    )))
}

fn find_theorem(tokens: &[SourceToken], name: &str) -> Result<FunctionSource, ClickError> {
    for (index, token) in tokens.iter().enumerate() {
        if token.text != "theorem"
            || tokens.get(index + 1).map(|token| token.text.as_str()) != Some(name)
        {
            continue;
        }
        let mut parameters_open = index + 2;
        if tokens.get(parameters_open).map(|token| token.text.as_str()) == Some("<") {
            parameters_open = matching_delimiter(tokens, parameters_open, "<", ">")? + 1;
        }
        if tokens.get(parameters_open).map(|token| token.text.as_str()) != Some("(") {
            continue;
        }
        let parameters_close = matching_delimiter(tokens, parameters_open, "(", ")")?;
        let mut body_open = parameters_close + 1;
        if tokens.get(body_open).map(|token| token.text.as_str()) == Some("executes") {
            let arguments_open = body_open + 2;
            body_open = matching_delimiter(tokens, arguments_open, "(", ")")? + 1;
        }
        if tokens.get(body_open).map(|token| token.text.as_str()) != Some("{") {
            continue;
        }
        let body_close = matching_delimiter(tokens, body_open, "{", "}")?;
        return Ok(FunctionSource {
            body_open,
            body_close,
        });
    }
    Err(ClickError::new(format!(
        "could not locate Click theorem `{name}`"
    )))
}

fn find_ensure_proof_edit(
    tokens: &[SourceToken],
    body_open: usize,
    body_close: usize,
    wanted: usize,
) -> Result<ProofSourceEdit, ClickError> {
    let mut depth = 0;
    let mut found = 0;
    let mut index = body_open + 1;
    while index < body_close {
        match tokens[index].text.as_str() {
            "{" => depth += 1,
            "}" => depth -= 1,
            "ensures"
                if depth == 0
                    && tokens
                        .get(index.wrapping_sub(1))
                        .map(|token| token.text.as_str())
                        != Some("exceptional") =>
            {
                if found == wanted {
                    return find_proof_edit_after(tokens, index, body_close);
                }
                found += 1;
            }
            "owns" | "produces" if depth == 0 => {
                if found == wanted {
                    return find_proof_edit_after(tokens, index, body_close);
                }
                found += 1;
            }
            _ => {}
        }
        index += 1;
    }
    Err(ClickError::new(format!(
        "could not locate source ensure {wanted}"
    )))
}

fn find_exceptional_ensure_proof_edit(
    tokens: &[SourceToken],
    body_open: usize,
    body_close: usize,
    wanted: usize,
) -> Result<ProofSourceEdit, ClickError> {
    let mut depth = 0;
    let mut found = 0;
    let mut index = body_open + 1;
    while index < body_close {
        match tokens[index].text.as_str() {
            "{" => depth += 1,
            "}" => depth -= 1,
            "exceptional"
                if depth == 0
                    && tokens.get(index + 1).map(|token| token.text.as_str())
                        == Some("ensures") =>
            {
                if found == wanted {
                    return find_proof_edit_after(tokens, index + 1, body_close);
                }
                found += 1;
            }
            _ => {}
        }
        index += 1;
    }
    Err(ClickError::new(format!(
        "could not locate source exceptional ensure {wanted}"
    )))
}

fn find_proof_edit_after(
    tokens: &[SourceToken],
    clause_start: usize,
    limit: usize,
) -> Result<ProofSourceEdit, ClickError> {
    let mut cursor = clause_start + 1;
    let mut nested = 0;
    while cursor < limit {
        match tokens[cursor].text.as_str() {
            "{" | "(" | "[" => nested += 1,
            "}" | ")" | "]" => nested -= 1,
            "by" if nested == 0 => {
                return Ok(ProofSourceEdit::Explicit(proof_span(tokens, cursor)?));
            }
            ";" if nested == 0 => {
                return Ok(ProofSourceEdit::DefaultTerminator {
                    span: tokens[cursor].span.clone(),
                    selector: tokens[clause_start].span.start,
                });
            }
            _ => {}
        }
        cursor += 1;
    }
    Err(ClickError::new("could not locate source proof terminator"))
}

fn find_grouped_proof_span(
    tokens: &[SourceToken],
    function: &FunctionSource,
) -> Result<Range<usize>, ClickError> {
    let by = function.body_close + 1;
    if tokens.get(by).map(|token| token.text.as_str()) != Some("by") {
        return Err(ClickError::new(
            "function uses grouped verification but has no source `by` clause",
        ));
    }
    proof_span(tokens, by)
}

fn find_claim_proof_span(
    tokens: &[SourceToken],
    function: &FunctionSource,
    claim: CProofClaim,
) -> Result<Range<usize>, ClickError> {
    match find_claim_proof_edit(tokens, function, claim)? {
        ProofSourceEdit::Explicit(span) => Ok(span),
        ProofSourceEdit::DefaultTerminator { .. } => Err(ClickError::new(format!(
            "selected {claim:?} uses a default proof and has no explicit source tactic"
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
    claim: CProofClaim,
) -> Result<ProofSourceEdit, ClickError> {
    match claim {
        CProofClaim::Ensure(index) => {
            find_ensure_proof_edit(tokens, function.body_open, function.body_close, index)
        }
        CProofClaim::ExceptionalEnsure(index) => find_exceptional_ensure_proof_edit(
            tokens,
            function.body_open,
            function.body_close,
            index,
        ),
        CProofClaim::Grouped => Err(ClickError::new(format!(
            "could not locate source clause for {claim:?}"
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
}

impl ExpansionCapture {
    pub(super) fn for_tactic(site: ProofSite, source_index: usize) -> Self {
        Self {
            site,
            source_index: Some(source_index),
            active: false,
            result: None,
            dropped_path_occurrence: false,
        }
    }

    pub(super) fn for_site(site: ProofSite) -> Self {
        Self {
            site,
            source_index: None,
            active: false,
            result: None,
            dropped_path_occurrence: false,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum ProofSite {
    FunctionClaim {
        function_name: String,
        claim: CProofClaim,
    },
    TheoremEnsure {
        theorem_name: String,
        ensure_index: usize,
    },
    LoopPhase {
        function_name: String,
        loop_index: usize,
        phase: &'static str,
    },
}

impl ProofSite {
    pub(super) fn description(&self) -> String {
        match self {
            Self::FunctionClaim {
                function_name,
                claim,
            } => format!("function `{function_name}` {claim:?}"),
            Self::TheoremEnsure {
                theorem_name,
                ensure_index,
            } => format!("theorem `{theorem_name}` ensure {ensure_index}"),
            Self::LoopPhase {
                function_name,
                loop_index,
                phase,
            } => format!("`{function_name}.loop({loop_index}).{phase}`"),
        }
    }
}

#[derive(Clone, Debug)]
enum TacticSourceEdit {
    Partial(Range<usize>),
    PartialProofClause(Range<usize>),
    WholeProof(ProofSourceEdit),
}

#[derive(Clone, Debug)]
struct LocatedSourceTactic {
    site: ProofSite,
    source_index: usize,
    edit: TacticSourceEdit,
}

fn locate_source_tactic(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<LocatedSourceTactic, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    locate_source_tactic_context(click_source, &sources, line, column)
}

fn locate_source_tactic_context(
    click_source: &str,
    c_sources: &CSourceContext<'_>,
    line: usize,
    column: usize,
) -> Result<LocatedSourceTactic, ClickError> {
    let file = parse_source_with_c_layouts_context(click_source, c_sources)?;
    locate_source_tactic_file(click_source, &file, line, column)
}

fn locate_source_tactic_file(
    click_source: &str,
    file: &ClickFile,
    line: usize,
    column: usize,
) -> Result<LocatedSourceTactic, ClickError> {
    let wanted = offset_at_position(click_source, line, column)?;
    let tokens = scan_source_tokens(click_source)?;
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        let source = find_theorem(&tokens, theorem.name())?;
        for (ensure_index, ensure) in theorem.ensures().iter().enumerate() {
            let edit =
                find_ensure_proof_edit(&tokens, source.body_open, source.body_close, ensure_index)?;
            let site = ProofSite::TheoremEnsure {
                theorem_name: theorem.name().to_string(),
                ensure_index,
            };
            if let Some(found) =
                locate_tactic_in_proof(&tokens, &edit, ensure.proof(), wanted, site)?
            {
                return Ok(found);
            }
        }
    }
    for function_block in file.function_blocks() {
        let function_name = function_block.signature().name();
        let function = find_function(&tokens, function_name)?;
        for clause in function_block.structural_clauses() {
            if let CodeRegion::Loop(loop_index) = clause.region() {
                for (phase, proof) in [
                    ("initialize", clause.initialize_proof()),
                    ("preserve", clause.preserve_proof()),
                ] {
                    let (selector, proof_span, insertion) =
                        find_loop_phase_proof_span(&tokens, &function, *loop_index, phase)?;
                    let default_proof = SourceProof::Default;
                    let proof = proof.unwrap_or(&default_proof);
                    let edit = proof_span.map_or_else(
                        || ProofSourceEdit::OmittedLoopPhase {
                            span: insertion..insertion,
                            selector,
                            phase,
                        },
                        ProofSourceEdit::Explicit,
                    );
                    if let Some(found) = locate_tactic_in_proof(
                        &tokens,
                        &edit,
                        proof,
                        wanted,
                        ProofSite::LoopPhase {
                            function_name: function_name.to_string(),
                            loop_index: *loop_index,
                            phase,
                        },
                    )? {
                        return Ok(found);
                    }
                }
            }
            let block = find_structural_clause_block(&tokens, &function, *clause.region())?;
            let edits = structural_item_proof_edits(&tokens, &block)?;
            if edits.len() != clause.items().len() {
                return Err(ClickError::new(format!(
                    "structural source mapping for `{function_name}` {:?} found {} items, expected {}",
                    clause.region(),
                    edits.len(),
                    clause.items().len()
                )));
            }
        }
        if let Some(proof) = function_block.grouped_proof() {
            let edit = ProofSourceEdit::Explicit(find_grouped_proof_span(&tokens, &function)?);
            if let Some(found) = locate_tactic_in_proof(
                &tokens,
                &edit,
                proof,
                wanted,
                ProofSite::FunctionClaim {
                    function_name: function_name.to_string(),
                    claim: CProofClaim::Grouped,
                },
            )? {
                return Ok(found);
            }
            continue;
        }
        for (index, ensure) in function_block.ensures().iter().enumerate() {
            let claim = CProofClaim::Ensure(index);
            let edit = find_claim_proof_edit(&tokens, &function, claim)?;
            if let Some(found) = locate_tactic_in_proof(
                &tokens,
                &edit,
                ensure.proof(),
                wanted,
                ProofSite::FunctionClaim {
                    function_name: function_name.to_string(),
                    claim,
                },
            )? {
                return Ok(found);
            }
        }
        for (index, ensure) in function_block.exceptional_ensures().iter().enumerate() {
            let claim = CProofClaim::ExceptionalEnsure(index);
            let edit = find_claim_proof_edit(&tokens, &function, claim)?;
            if let Some(found) = locate_tactic_in_proof(
                &tokens,
                &edit,
                ensure.proof(),
                wanted,
                ProofSite::FunctionClaim {
                    function_name: function_name.to_string(),
                    claim,
                },
            )? {
                return Ok(found);
            }
        }
    }
    Err(ClickError::new(format!(
        "no explicit C proof tactic starts at {line}:{column}"
    )))
}

/// Whether the smart tactic written at `target` is a direct tactic of the
/// body of the `have` written at `have`.
///
/// A `have` whose body is a smart tactic is one source site anchored at its
/// `have` keyword: the `have` owns its nested proof work, and expanding it
/// rewrites that body. A location naming the smart tactic inside the body
/// selects that same site.
pub fn smart_have_body_tactic_at(
    source: &str,
    have: &SourcePosition,
    target: &SourcePosition,
) -> Result<bool, ClickError> {
    let tokens = scan_source_tokens(source)?;
    let have = offset_at_position(source, have.line, have.column)?;
    let target = offset_at_position(source, target.line, target.column)?;
    let Some(start) = tokens.iter().position(|token| token.span.start == have) else {
        return Ok(false);
    };
    have_body_smart_tactic_starts_at(&tokens, start, target)
}

fn have_body_smart_tactic_starts_at(
    tokens: &[SourceToken],
    start: usize,
    target: usize,
) -> Result<bool, ClickError> {
    if tokens[start].text != "have" {
        return Ok(false);
    }
    let end = tactic_end_token(tokens, start, tokens.len())?;
    let Some(by) = (start..=end).find(|&index| tokens[index].text == "by") else {
        return Ok(false);
    };
    let starts = if tokens.get(by + 1).map(|token| token.text.as_str()) == Some("{") {
        let close = matching_delimiter(tokens, by + 1, "{", "}")?;
        direct_tactic_token_ranges(tokens, by + 1, close)?
            .into_iter()
            .map(|range| range.start)
            .collect::<Vec<_>>()
    } else {
        vec![by + 1]
    };
    Ok(starts.into_iter().any(|index| {
        tokens[index].span.start == target && matches!(tokens[index].text.as_str(), "simp" | "auto")
    }))
}

/// The source index of the smart `have` site whose body writes the smart
/// tactic starting at `wanted`, if there is one.
fn smart_have_owning_tactic_at(
    tokens: &[SourceToken],
    spans: &[Range<usize>],
    tactics: &[ProofTactic],
    wanted: usize,
) -> Result<Option<usize>, ClickError> {
    let mut sites = Vec::new();
    collect_smart_script_sites("", tactics, 0, &mut sites);
    for site in sites {
        let Some(span) = spans.get(site.source_index) else {
            continue;
        };
        if !span.contains(&wanted) {
            continue;
        }
        let Some(start) = tokens
            .iter()
            .position(|token| token.span.start == span.start)
        else {
            continue;
        };
        if have_body_smart_tactic_starts_at(tokens, start, wanted)? {
            return Ok(Some(site.source_index));
        }
    }
    Ok(None)
}

fn locate_tactic_in_proof(
    tokens: &[SourceToken],
    edit: &ProofSourceEdit,
    proof: &SourceProof,
    wanted: usize,
    site: ProofSite,
) -> Result<Option<LocatedSourceTactic>, ClickError> {
    match proof {
        SourceProof::Script(tactics) => {
            let ProofSourceEdit::Explicit(source_proof_span) = edit else {
                return Err(ClickError::new(
                    "an explicit proof script has no source `by` clause",
                ));
            };
            let spans = collect_source_tactic_spans(tokens, source_proof_span, tactics)?;
            let exact = spans.iter().position(|span| span.start == wanted);
            let selected = match exact {
                Some(index) => Some(index),
                None => smart_have_owning_tactic_at(tokens, &spans, tactics, wanted)?,
            };
            let Some((source_index, span)) = selected.map(|index| (index, spans[index].clone()))
            else {
                return Ok(None);
            };
            let edit = if source_tactic_is_nested_proof_clause(tactics, source_index) {
                let tactic_token = tokens
                    .iter()
                    .position(|token| token.span.start == span.start)
                    .ok_or_else(|| ClickError::new("could not locate selected nested tactic"))?;
                let by = tactic_token.checked_sub(1).ok_or_else(|| {
                    ClickError::new("selected nested tactic has no source `by` clause")
                })?;
                if tokens[by].text != "by" {
                    return Err(ClickError::new(
                        "selected nested tactic has no source `by` clause",
                    ));
                }
                TacticSourceEdit::PartialProofClause(proof_span(tokens, by)?)
            } else {
                TacticSourceEdit::Partial(span)
            };
            Ok(Some(LocatedSourceTactic {
                site,
                source_index,
                edit,
            }))
        }
        SourceProof::Tactic(_) => match edit {
            ProofSourceEdit::Explicit(proof_span) => {
                let by = tokens
                    .iter()
                    .position(|token| token.span.start == proof_span.start && token.text == "by")
                    .ok_or_else(|| ClickError::new("could not locate source `by` clause"))?;
                Ok(tokens
                    .get(by + 1)
                    .filter(|token| token.span.start == wanted)
                    .map(|_| LocatedSourceTactic {
                        site,
                        source_index: 0,
                        edit: TacticSourceEdit::WholeProof(edit.clone()),
                    }))
            }
            ProofSourceEdit::DefaultTerminator { .. }
            | ProofSourceEdit::OmittedLoopPhase { .. } => {
                Ok((edit.selector() == wanted).then(|| LocatedSourceTactic {
                    site,
                    source_index: 0,
                    edit: TacticSourceEdit::WholeProof(edit.clone()),
                }))
            }
        },
        SourceProof::Default => Ok((edit.selector() == wanted).then(|| LocatedSourceTactic {
            site,
            source_index: 0,
            edit: TacticSourceEdit::WholeProof(edit.clone()),
        })),
    }
}

pub fn c0_tactic_source_position(
    click_source: &str,
    c_sources: &[(&str, &str)],
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    c0_tactic_source_position_context(&sources, click_source, claim_label, source_index)
}

pub fn c0_prepared_tactic_source_position(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::prepared(imports);
    c0_tactic_source_position_context(&sources, click_source, claim_label, source_index)
}

pub fn cpp_prepared_tactic_source_position(
    click_source: &str,
    import: &crate::languages::cpp::PreparedCppImport,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::cpp(import)?;
    c0_tactic_source_position_context(&sources, click_source, claim_label, source_index)
}

pub fn c0_project_tactic_source_position(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::bundle(c_sources).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_tactic_source_position_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
        source_index,
    )
}

pub fn c0_prepared_project_tactic_source_position(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::prepared(imports).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_tactic_source_position_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
        source_index,
    )
}

pub fn cpp_prepared_project_tactic_source_position(
    project: &ClickProject,
    import: &crate::languages::cpp::PreparedCppImport,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::cpp(import)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_tactic_source_position_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
        source_index,
    )
}

fn c0_tactic_source_position_context(
    c_sources: &CSourceContext<'_>,
    click_source: &str,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let file = parse_source_with_c_layouts_context(click_source, c_sources)?;
    c0_tactic_source_position_file(&file, click_source, claim_label, source_index)
}

fn c0_tactic_source_position_file(
    file: &ClickFile,
    click_source: &str,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        let source = find_theorem(&tokens, theorem.name())?;
        for (ensure_index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{ensure_index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            let execution_claim = theorem.executes.is_some()
                && ensure_index == 0
                && claim_label == format!("{}.contract", theorem.name());
            if label != claim_label && !execution_claim {
                continue;
            }
            let edit =
                find_ensure_proof_edit(&tokens, source.body_open, source.body_close, ensure_index)?;
            return proof_source_position(
                click_source,
                &tokens,
                match &edit {
                    ProofSourceEdit::Explicit(span) => Some(span),
                    ProofSourceEdit::DefaultTerminator { .. }
                    | ProofSourceEdit::OmittedLoopPhase { .. } => None,
                },
                Some(ensure.proof()),
                edit.selector(),
                claim_label,
                source_index,
            );
        }
    }
    for function_block in file.function_blocks() {
        let function_name = function_block.signature().name();
        let function = find_function(&tokens, function_name)?;
        for clause in function_block.structural_clauses() {
            let block = find_structural_clause_block(&tokens, &function, *clause.region())?;
            let edits = structural_item_proof_edits(&tokens, &block)?;
            if edits.len() != clause.items().len() {
                return Err(ClickError::new(format!(
                    "structural source mapping for `{function_name}` {:?} found {} items, expected {}",
                    clause.region(),
                    edits.len(),
                    clause.items().len()
                )));
            }
        }
        if let Some(rest) = claim_label
            .strip_prefix(function_name)
            .and_then(|rest| rest.strip_prefix(".loop("))
            && let Some((loop_index, phase)) = rest.split_once(").")
            && matches!(phase, "initialize" | "preserve")
            && let Ok(loop_index) = loop_index.parse::<usize>()
            && let Some(clause) = function_block
                .structural_clauses()
                .iter()
                .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        {
            let proof = if phase == "initialize" {
                clause.initialize_proof()
            } else {
                clause.preserve_proof()
            };
            let (fallback, proof_span, _) =
                find_loop_phase_proof_span(&tokens, &function, loop_index, phase)?;
            return proof_source_position(
                click_source,
                &tokens,
                proof_span.as_ref(),
                proof,
                fallback,
                claim_label,
                source_index,
            );
        }
        let selected = if claim_label == format!("{function_name}.contract") {
            function_block
                .grouped_proof()
                .map(|proof| (CProofClaim::Grouped, proof))
        } else {
            function_block
                .ensures()
                .iter()
                .enumerate()
                .find_map(|(index, ensure)| {
                    let label = ensure.name().map_or_else(
                        || format!("{function_name}.ensures_{index}"),
                        |name| format!("{function_name}.{name}"),
                    );
                    (label == claim_label).then_some((CProofClaim::Ensure(index), ensure.proof()))
                })
                .or_else(|| {
                    function_block
                        .exceptional_ensures()
                        .iter()
                        .enumerate()
                        .find_map(|(index, ensure)| {
                            let label = ensure.name().map_or_else(
                                || format!("{function_name}.exceptional_ensures_{index}"),
                                |name| format!("{function_name}.{name}"),
                            );
                            (label == claim_label)
                                .then_some((CProofClaim::ExceptionalEnsure(index), ensure.proof()))
                        })
                })
        };
        let Some((claim, proof)) = selected else {
            continue;
        };
        let fallback = match claim {
            CProofClaim::Grouped => tokens[function.body_close].span.start,
            CProofClaim::Ensure(_) | CProofClaim::ExceptionalEnsure(_) => {
                find_claim_clause_offset(&tokens, &function, claim)?
            }
        };
        let proof_span = match claim {
            CProofClaim::Grouped => Some(find_grouped_proof_span(&tokens, &function)?),
            CProofClaim::Ensure(_) | CProofClaim::ExceptionalEnsure(_) => {
                find_claim_proof_span(&tokens, &function, claim).ok()
            }
        };
        return proof_source_position(
            click_source,
            &tokens,
            proof_span.as_ref(),
            Some(proof),
            fallback,
            claim_label,
            source_index,
        );
    }
    Err(ClickError::new(format!(
        "could not locate source proof `{claim_label}`"
    )))
}

fn proof_source_position(
    click_source: &str,
    tokens: &[SourceToken],
    proof_span: Option<&Range<usize>>,
    proof: Option<&SourceProof>,
    fallback: usize,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    if let Some(tactics) = proof.and_then(SourceProof::tactics) {
        let proof_span = proof_span.ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` has no explicit source proof clause"
            ))
        })?;
        let spans = collect_source_tactic_spans(tokens, proof_span, tactics)?;
        let span = spans.get(source_index).ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` has no source tactic occurrence {source_index}"
            ))
        })?;
        return Ok(position_at_offset(click_source, span.start));
    }
    if source_index != 0 {
        return Err(ClickError::new(format!(
            "`{claim_label}` has no source tactic occurrence {source_index}"
        )));
    }
    if let Some(proof_span) = proof_span {
        let by = tokens
            .iter()
            .position(|token| token.span.start == proof_span.start && token.text == "by")
            .ok_or_else(|| ClickError::new("could not locate source `by` clause"))?;
        if let Some(tactic) = tokens.get(by + 1) {
            return Ok(position_at_offset(click_source, tactic.span.start));
        }
    }
    Ok(position_at_offset(click_source, fallback))
}

fn find_claim_clause_offset(
    tokens: &[SourceToken],
    function: &FunctionSource,
    claim: CProofClaim,
) -> Result<usize, ClickError> {
    Ok(find_claim_proof_edit(tokens, function, claim)?.selector())
}

fn find_loop_phase_proof_span(
    tokens: &[SourceToken],
    function: &FunctionSource,
    wanted_loop: usize,
    phase: &str,
) -> Result<(usize, Option<Range<usize>>, usize), ClickError> {
    let mut depth = 0;
    let mut index = function.body_open + 1;
    while index < function.body_close {
        match tokens[index].text.as_str() {
            "{" => depth += 1,
            "}" => depth -= 1,
            "for"
                if depth == 0
                    && tokens.get(index + 1).map(|token| token.text.as_str()) == Some("loop")
                    && tokens.get(index + 2).map(|token| token.text.as_str()) == Some("(") =>
            {
                let loop_index = tokens
                    .get(index + 3)
                    .and_then(|token| token.text.parse::<usize>().ok());
                let mut open = index + 5;
                if tokens.get(open).map(|token| token.text.as_str()) == Some("as") {
                    open += 2;
                }
                if loop_index == Some(wanted_loop)
                    && tokens.get(index + 4).map(|token| token.text.as_str()) == Some(")")
                    && tokens.get(open).map(|token| token.text.as_str()) == Some("{")
                {
                    let selector = if phase == "initialize" {
                        tokens[index].span.start
                    } else {
                        tokens[index + 1].span.start
                    };
                    let close = matching_delimiter(tokens, open, "{", "}")?;
                    let mut nested = 0;
                    for cursor in open + 1..close {
                        match tokens[cursor].text.as_str() {
                            "{" => nested += 1,
                            "}" => nested -= 1,
                            text if nested == 0 && text == phase => {
                                let by = cursor + 1;
                                if tokens.get(by).map(|token| token.text.as_str()) != Some("by") {
                                    return Err(ClickError::new(format!(
                                        "`{phase}` has no source `by` clause"
                                    )));
                                }
                                return Ok((
                                    selector,
                                    Some(proof_span(tokens, by)?),
                                    tokens[close].span.start,
                                ));
                            }
                            _ => {}
                        }
                    }
                    return Ok((selector, None, tokens[close].span.start));
                }
            }
            _ => {}
        }
        index += 1;
    }
    Err(ClickError::new(format!(
        "could not locate source loop({wanted_loop})"
    )))
}

fn parse_source_with_c_layouts(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<ClickFile, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    parse_source_with_c_layouts_context(click_source, &sources)
}

fn parse_source_with_c_layouts_context(
    click_source: &str,
    sources: &CSourceContext<'_>,
) -> Result<ClickFile, ClickError> {
    let (
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
        local_struct_pointers,
    ) = parse_c_layouts(click_source, sources)?;
    parser::parse_with_layouts_and_aggregate_objects(
        click_source,
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
        local_struct_pointers,
    )
}

fn find_structural_clause_block(
    tokens: &[SourceToken],
    function: &FunctionSource,
    wanted: CodeRegion,
) -> Result<Range<usize>, ClickError> {
    let mut depth = 0;
    let mut index = function.body_open + 1;
    while index < function.body_close {
        match tokens[index].text.as_str() {
            "{" => depth += 1,
            "}" => depth -= 1,
            "for" if depth == 0 => {
                let kind = tokens.get(index + 1).map(|token| token.text.as_str());
                let region = match kind {
                    Some("loop" | "statement")
                        if tokens.get(index + 2).map(|token| token.text.as_str()) == Some("(") =>
                    {
                        let region_index = tokens
                            .get(index + 3)
                            .and_then(|token| token.text.parse::<usize>().ok());
                        if tokens.get(index + 4).map(|token| token.text.as_str()) != Some(")") {
                            None
                        } else {
                            region_index.map(|region_index| {
                                if kind == Some("loop") {
                                    CodeRegion::Loop(region_index)
                                } else {
                                    CodeRegion::Statement(region_index)
                                }
                            })
                        }
                    }
                    _ => None,
                };
                let mut open = index + 5;
                if tokens.get(open).map(|token| token.text.as_str()) == Some("as") {
                    open += 2;
                }
                if region == Some(wanted)
                    && tokens.get(open).map(|token| token.text.as_str()) == Some("{")
                {
                    let close = matching_delimiter(tokens, open, "{", "}")?;
                    return Ok(open..close);
                }
            }
            _ => {}
        }
        index += 1;
    }
    Err(ClickError::new(format!(
        "could not locate structural source block {wanted:?}"
    )))
}

fn structural_item_proof_edits(
    tokens: &[SourceToken],
    block: &Range<usize>,
) -> Result<Vec<ProofSourceEdit>, ClickError> {
    fn token_after_edit(tokens: &[SourceToken], edit: &ProofSourceEdit) -> usize {
        tokens
            .iter()
            .position(|token| token.span.end == edit.span().end)
            .map_or(tokens.len(), |index| index + 1)
    }

    let mut edits = Vec::new();
    let mut cursor = block.start + 1;
    while cursor < block.end {
        match tokens[cursor].text.as_str() {
            "initialize" | "preserve" => {
                let by = cursor + 1;
                if tokens.get(by).map(|token| token.text.as_str()) != Some("by") {
                    return Err(ClickError::new(
                        "loop phase is missing its source `by` clause",
                    ));
                }
                let phase = ProofSourceEdit::Explicit(proof_span(tokens, by)?);
                cursor = token_after_edit(tokens, &phase);
            }
            "invariant" | "assert" | "immutable" | "mutable" => {
                let edit = find_proof_edit_after(tokens, cursor, block.end)?;
                cursor = token_after_edit(tokens, &edit);
                edits.push(edit);
            }
            "step" if tokens.get(cursor + 1).map(|token| token.text.as_str()) == Some("{") => {
                let open = cursor + 1;
                let close = matching_delimiter(tokens, open, "{", "}")?;
                let mut item = open + 1;
                while item < close {
                    if matches!(tokens[item].text.as_str(), "immutable" | "mutable") {
                        let edit = find_proof_edit_after(tokens, item, close)?;
                        item = token_after_edit(tokens, &edit);
                        edits.push(edit);
                    } else {
                        item += 1;
                    }
                }
                cursor = close + 1;
            }
            _ => cursor += 1,
        }
    }
    Ok(edits)
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

/// Resolve positions inside written `have` and `open` bodies. The first
/// position is the enclosing tactic, as reported by the usual claim mapper;
/// each index then selects a direct tactic in that body's source block.
pub fn nested_tactic_source_position(
    source: &str,
    outer: &SourcePosition,
    nested_indices: &[usize],
) -> Result<SourcePosition, ClickError> {
    let tokens = scan_source_tokens(source)?;
    let offset = offset_at_position(source, outer.line, outer.column)?;
    let mut current = tokens
        .iter()
        .position(|token| token.span.start == offset)
        .ok_or_else(|| ClickError::new("could not locate enclosing source tactic"))?;
    for &index in nested_indices {
        let kind = tokens[current].text.as_str();
        if !matches!(kind, "have" | "open") {
            return Err(ClickError::new(format!(
                "source `{kind}` has no nested `have` or `open` tactic body"
            )));
        }
        let mut depths = [0_usize; 3];
        let mut body_open = None;
        for cursor in current + 1..tokens.len() {
            let token = tokens[cursor].text.as_str();
            if depths == [0; 3] {
                if kind == "have"
                    && token == "by"
                    && tokens.get(cursor + 1).map(|token| token.text.as_str()) == Some("{")
                {
                    body_open = Some(cursor + 1);
                    break;
                }
                if kind == "open" && token == "{" {
                    body_open = Some(cursor);
                    break;
                }
                if token == ";" {
                    break;
                }
            }
            match token {
                "(" => depths[0] += 1,
                ")" => depths[0] = depths[0].saturating_sub(1),
                "[" => depths[1] += 1,
                "]" => depths[1] = depths[1].saturating_sub(1),
                "{" => depths[2] += 1,
                "}" => depths[2] = depths[2].saturating_sub(1),
                _ => {}
            }
        }
        let open = body_open.ok_or_else(|| {
            ClickError::new(format!("could not locate source `{kind}` tactic body"))
        })?;
        let close = matching_delimiter(&tokens, open, "{", "}")?;
        let ranges = direct_tactic_token_ranges(&tokens, open, close)?;
        current = ranges
            .get(index)
            .ok_or_else(|| ClickError::new(format!("nested source tactic {index} is missing")))?
            .start;
    }
    Ok(position_at_offset(source, tokens[current].span.start))
}

/// Return the exact written tactic beginning at a diagnostic source position.
/// The position is resolved by the same source mapper used for proof steps.
pub fn tactic_source_at_position(
    source: &str,
    position: &SourcePosition,
) -> Result<String, ClickError> {
    let tokens = scan_source_tokens(source)?;
    let offset = offset_at_position(source, position.line, position.column)?;
    let start = tokens
        .iter()
        .position(|token| token.span.start == offset)
        .ok_or_else(|| ClickError::new("could not locate source tactic"))?;
    let end = tactic_end_token(&tokens, start, tokens.len())?;
    Ok(source[tokens[start].span.start..tokens[end].span.end].to_string())
}

/// Select the written arm containing a trace target inside a two-arm tactic.
/// Returning `None` means the target lies outside both arms (for example, in
/// the continuation after a completed branch).
pub fn tactic_arm_containing_position(
    source: &str,
    tactic_position: &SourcePosition,
    target_position: &SourcePosition,
) -> Result<Option<usize>, ClickError> {
    let tokens = scan_source_tokens(source)?;
    let tactic_offset = offset_at_position(source, tactic_position.line, tactic_position.column)?;
    let target_offset = offset_at_position(source, target_position.line, target_position.column)?;
    let start = tokens
        .iter()
        .position(|token| token.span.start == tactic_offset)
        .ok_or_else(|| ClickError::new("could not locate trace branch tactic"))?;
    let end = tactic_end_token(&tokens, start, tokens.len())?;
    let range = start..end + 1;
    let blocks = match tokens[start].text.as_str() {
        "branch" => find_branch_blocks(&tokens, &range)?,
        "if" => find_if_branch_blocks(&tokens, &range)?,
        "outcomes" => find_named_arm_blocks(&tokens, &range, "returned", "threw", "outcomes")?,
        _ => return Ok(None),
    };
    for (index, (open, close)) in [(blocks.0, blocks.1), (blocks.2, blocks.3)]
        .into_iter()
        .enumerate()
    {
        if tokens[open].span.start < target_offset && target_offset < tokens[close].span.end {
            return Ok(Some(index));
        }
    }
    Ok(None)
}

/// Whether a selected tactic is inside the proof body of a written `have`.
/// A completed `have` exports its proposition, not the body's intermediate
/// facts; the trace only enters that body when it contains the target.
pub fn tactic_have_body_contains_position(
    source: &str,
    tactic_position: &SourcePosition,
    target_position: &SourcePosition,
) -> Result<bool, ClickError> {
    let tokens = scan_source_tokens(source)?;
    let tactic_offset = offset_at_position(source, tactic_position.line, tactic_position.column)?;
    let target_offset = offset_at_position(source, target_position.line, target_position.column)?;
    let start = tokens
        .iter()
        .position(|token| token.span.start == tactic_offset)
        .ok_or_else(|| ClickError::new("could not locate trace have tactic"))?;
    if tokens[start].text != "have" {
        return Ok(false);
    }
    let end = tactic_end_token(&tokens, start, tokens.len())?;
    let Some(by) = (start..=end).find(|&index| tokens[index].text == "by") else {
        return Ok(false);
    };
    let Some(open) = (by + 1..=end).find(|&index| tokens[index].text == "{") else {
        return Ok(false);
    };
    let close = matching_delimiter(&tokens, open, "{", "}")?;
    Ok(tokens[open].span.start < target_offset && target_offset < tokens[close].span.end)
}

/// Whether another written tactic starts on the same source line. Inspect
/// tactic blocks through the source tokenizer, so semicolons inside a tactic
/// or its nested expressions are not mistaken for sibling tactics.
pub fn tactic_line_has_multiple_starts(
    source: &str,
    position: &SourcePosition,
) -> Result<bool, ClickError> {
    let selected = offset_at_position(source, position.line, position.column)?;
    let mut starts = tactic_starts_on_line(source, position.line)?;
    if !starts.iter().any(|start| start.column == position.column) {
        starts.push(position_at_offset(source, selected));
    }
    if starts.len() <= 1 {
        return Ok(false);
    }
    // A one-line `have ... by { simp(); }` has two lexical tactic starts,
    // but the outer `have` is still the one unambiguous top-level tactic on
    // that line. Keep a column for the nested tactic, or for sibling tactics.
    if starts
        .first()
        .is_none_or(|start| start.column != position.column)
    {
        return Ok(true);
    }
    let tokens = scan_source_tokens(source)?;
    let Some(start) = tokens.iter().position(|token| token.span.start == selected) else {
        return Ok(true);
    };
    let end = tactic_end_token(&tokens, start, tokens.len())?;
    Ok(starts.iter().skip(1).any(|start| {
        offset_at_position(source, start.line, start.column)
            .is_ok_and(|offset| offset >= tokens[end].span.end)
    }))
}

/// Candidate written tactic starts on a Click source line, for selecting a
/// trace target without requiring a column when the line is unambiguous.
pub fn tactic_starts_on_line(source: &str, line: usize) -> Result<Vec<SourcePosition>, ClickError> {
    let tokens = scan_source_tokens(source)?;
    let mut starts = std::collections::BTreeSet::new();
    for (open, token) in tokens.iter().enumerate() {
        if token.text != "{" {
            continue;
        }
        let preceding = open.checked_sub(1).and_then(|index| tokens.get(index));
        // A match arm's block follows `=>`, which the scanner emits as the
        // two punctuation tokens `=` and `>`.
        let arm_block = open >= 2 && tokens[open - 2].text == "=" && tokens[open - 1].text == ">";
        let direct_proof_block = arm_block
            || preceding
                .is_some_and(|token| matches!(token.text.as_str(), "by" | "then" | "else" | "and"));
        let open_tactic_block = preceding.is_some_and(|token| token.text == ")")
            && tokens[..open]
                .iter()
                .rev()
                .take_while(|token| !matches!(token.text.as_str(), ";" | "{" | "}"))
                .any(|token| token.text == "open");
        if !direct_proof_block && !open_tactic_block {
            continue;
        }
        let Ok(close) = matching_delimiter(&tokens, open, "{", "}") else {
            continue;
        };
        let Ok(ranges) = direct_tactic_token_ranges(&tokens, open, close) else {
            continue;
        };
        for range in ranges {
            let start = tokens[range.start].span.start;
            if position_at_offset(source, start).line == line {
                starts.insert(start);
            }
        }
    }
    Ok(starts
        .into_iter()
        .map(|start| position_at_offset(source, start))
        .collect())
}

pub(super) fn position_at_offset(source: &str, offset: usize) -> SourcePosition {
    let prefix = &source[..offset];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let line_start = prefix.rfind('\n').map_or(0, |newline| newline + 1);
    let column = source[line_start..offset].chars().count() + 1;
    SourcePosition::new(line, column)
}

fn proof_span(tokens: &[SourceToken], by: usize) -> Result<Range<usize>, ClickError> {
    let start = tokens[by].span.start;
    let body = by + 1;
    let end_token = match tokens.get(body).map(|token| token.text.as_str()) {
        Some("{") => matching_delimiter(tokens, body, "{", "}")?,
        Some("auto" | "frame" | "simp") => body,
        _ => return Err(ClickError::new("unsupported source proof clause")),
    };
    let semicolon = end_token + 1;
    let end = if tokens.get(semicolon).map(|token| token.text.as_str()) == Some(";") {
        tokens[semicolon].span.end
    } else {
        tokens[end_token].span.end
    };
    Ok(start..end)
}

fn collect_source_tactic_spans(
    tokens: &[SourceToken],
    proof_span: &Range<usize>,
    tactics: &[ProofTactic],
) -> Result<Vec<Range<usize>>, ClickError> {
    let by = tokens
        .iter()
        .position(|token| token.span.start == proof_span.start && token.text == "by")
        .ok_or_else(|| ClickError::new("could not locate selected source proof"))?;
    let open = by + 1;
    if tokens.get(open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new(
            "individual tactic expansion requires an explicit `by { ... }` proof",
        ));
    }
    let close = matching_delimiter(tokens, open, "{", "}")?;
    let mut spans = Vec::new();
    collect_tactic_block_spans(tokens, open, close, tactics, &mut spans)?;
    Ok(spans)
}

fn source_tactic_is_nested_proof_clause(tactics: &[ProofTactic], wanted: usize) -> bool {
    fn in_proof(proof: &SourceProof, wanted: usize, source_index: usize) -> Option<bool> {
        match proof {
            SourceProof::Default => None,
            SourceProof::Tactic(_) => (wanted == source_index).then_some(true),
            SourceProof::Script(tactics) => find(tactics, wanted, source_index),
        }
    }

    fn find(tactics: &[ProofTactic], wanted: usize, offset: usize) -> Option<bool> {
        let mut source_index = offset;
        for tactic in tactics {
            if wanted == source_index {
                return Some(false);
            }
            let nested = match tactic {
                ProofTactic::Open(open) => find(&open.tactics, wanted, source_index + 1),
                ProofTactic::If(proof_if) => find(&proof_if.then_tactics, wanted, source_index + 1)
                    .or_else(|| {
                        find(
                            &proof_if.else_tactics,
                            wanted,
                            source_index + 1 + source_tactic_count(&proof_if.then_tactics),
                        )
                    }),
                ProofTactic::Branch(proof_branch) => {
                    find(&proof_branch.then_tactics, wanted, source_index + 1).or_else(|| {
                        find(
                            &proof_branch.else_tactics,
                            wanted,
                            source_index + 1 + source_tactic_count(&proof_branch.then_tactics),
                        )
                    })
                }
                ProofTactic::StructuralInduct { arms, .. } => {
                    let mut nested_source_index = source_index + 1;
                    let mut found = None;
                    for arm in arms {
                        found = find(&arm.tactics, wanted, nested_source_index);
                        nested_source_index += source_tactic_count(&arm.tactics);
                        if found.is_some() {
                            break;
                        }
                    }
                    found
                }
                ProofTactic::Match(proof_match) => {
                    let arms = &proof_match.arms;
                    let mut nested_source_index = source_index + 1;
                    let mut found = None;
                    for arm in arms {
                        found = find(&arm.tactics, wanted, nested_source_index);
                        nested_source_index += source_tactic_count(&arm.tactics);
                        if found.is_some() {
                            break;
                        }
                    }
                    found
                }
                ProofTactic::Loop(clause) => {
                    let mut nested_source_index = source_index + 1;
                    let mut found = None;
                    if let Some(proof) = clause.initialize_proof() {
                        found = in_proof(proof, wanted, nested_source_index);
                        nested_source_index += proof_source_tactic_count(proof);
                    }
                    if found.is_none()
                        && let Some(proof) = clause.preserve_proof()
                    {
                        found = in_proof(proof, wanted, nested_source_index);
                    }
                    found
                }
                _ => None,
            };
            if nested.is_some() {
                return nested;
            }
            source_index += source_tactic_count(std::slice::from_ref(tactic));
        }
        None
    }

    find(tactics, wanted, 0).unwrap_or(false)
}

fn collect_tactic_block_spans(
    tokens: &[SourceToken],
    open: usize,
    close: usize,
    tactics: &[ProofTactic],
    spans: &mut Vec<Range<usize>>,
) -> Result<(), ClickError> {
    let direct = direct_tactic_token_ranges(tokens, open, close)?;
    if direct.len() != tactics.len() {
        return Err(ClickError::new(format!(
            "source proof has {} direct tactic(s), but the parsed proof has {}",
            direct.len(),
            tactics.len()
        )));
    }
    for (tactic, token_range) in tactics.iter().zip(direct) {
        spans.push(tokens[token_range.start].span.start..tokens[token_range.end - 1].span.end);
        match tactic {
            ProofTactic::Open(proof_open) => {
                let body_open = (token_range.start + 1..token_range.end)
                    .find(|index| tokens[*index].text == "{")
                    .ok_or_else(|| ClickError::new("source `open` tactic has no body"))?;
                let body_close = matching_delimiter(tokens, body_open, "{", "}")?;
                collect_tactic_block_spans(
                    tokens,
                    body_open,
                    body_close,
                    &proof_open.tactics,
                    spans,
                )?;
            }
            ProofTactic::If(proof_if) => {
                let (then_open, then_close, else_open, else_close) =
                    find_if_branch_blocks(tokens, &token_range)?;
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
                let (then_open, then_close, else_open, else_close) =
                    find_branch_blocks(tokens, &token_range)?;
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
            ProofTactic::StructuralInduct { arms, .. } => {
                let arm_blocks = find_structural_induction_arm_blocks(tokens, &token_range)?;
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
            ProofTactic::Match(proof_match) => {
                let arms = &proof_match.arms;
                let arm_blocks = find_structural_induction_arm_blocks(tokens, &token_range)?;
                if arm_blocks.len() != arms.len() {
                    return Err(ClickError::new(format!(
                        "source structural induction has {} arm(s), but the parsed tactic has {}",
                        arm_blocks.len(),
                        arms.len()
                    )));
                }
                for (arm, (arm_open, arm_close)) in arms.iter().zip(arm_blocks) {
                    collect_tactic_block_spans(tokens, arm_open, arm_close, &arm.tactics, spans)?;
                }
            }
            ProofTactic::Loop(clause) => {
                let block_open = (token_range.start..token_range.end)
                    .find(|index| tokens[*index].text == "{")
                    .ok_or_else(|| ClickError::new("source `loop` tactic has no body"))?;
                let block_close = matching_delimiter(tokens, block_open, "{", "}")?;
                let block = block_open..block_close;
                for (phase, proof) in [
                    ("initialize", clause.initialize_proof()),
                    ("preserve", clause.preserve_proof()),
                ] {
                    if let Some(proof) = proof {
                        let edit = inline_loop_phase_proof_edit(tokens, &block, phase)?
                            .ok_or_else(|| {
                                ClickError::new(format!(
                                    "parsed frontier-local loop has `{phase}` proof but source block does not"
                                ))
                            })?;
                        collect_nested_proof_spans(tokens, &edit, proof, spans)?;
                    }
                }
                let edits = structural_item_proof_edits(tokens, &block)?;
                if edits.len() != clause.items().len() {
                    return Err(ClickError::new(format!(
                        "frontier-local loop source mapping found {} items, expected {}",
                        edits.len(),
                        clause.items().len()
                    )));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn inline_loop_phase_proof_edit(
    tokens: &[SourceToken],
    block: &Range<usize>,
    phase: &str,
) -> Result<Option<ProofSourceEdit>, ClickError> {
    let mut cursor = block.start + 1;
    while cursor < block.end {
        if tokens[cursor].text == phase {
            let by = cursor + 1;
            if tokens.get(by).map(|token| token.text.as_str()) != Some("by") {
                return Err(ClickError::new(format!(
                    "loop phase `{phase}` is missing its source `by` clause"
                )));
            }
            return Ok(Some(ProofSourceEdit::Explicit(proof_span(tokens, by)?)));
        }
        cursor += 1;
    }
    Ok(None)
}

fn collect_nested_proof_spans(
    tokens: &[SourceToken],
    edit: &ProofSourceEdit,
    proof: &SourceProof,
    spans: &mut Vec<Range<usize>>,
) -> Result<(), ClickError> {
    match proof {
        SourceProof::Default => Ok(()),
        SourceProof::Tactic(_) => {
            let ProofSourceEdit::Explicit(span) = edit else {
                return Err(ClickError::new(
                    "explicit nested loop tactic has no source `by` clause",
                ));
            };
            let by = tokens
                .iter()
                .position(|token| token.span.start == span.start && token.text == "by")
                .ok_or_else(|| ClickError::new("could not locate nested source `by` clause"))?;
            let tactic = tokens
                .get(by + 1)
                .ok_or_else(|| ClickError::new("nested source `by` clause has no tactic"))?;
            spans.push(tactic.span.clone());
            Ok(())
        }
        SourceProof::Script(tactics) => {
            let ProofSourceEdit::Explicit(span) = edit else {
                return Err(ClickError::new(
                    "explicit nested loop proof has no source `by` clause",
                ));
            };
            let by = tokens
                .iter()
                .position(|token| token.span.start == span.start && token.text == "by")
                .ok_or_else(|| ClickError::new("could not locate nested source `by` clause"))?;
            let open = by + 1;
            if tokens.get(open).map(|token| token.text.as_str()) != Some("{") {
                return Err(ClickError::new(
                    "nested loop proof script has no source block",
                ));
            }
            let close = matching_delimiter(tokens, open, "{", "}")?;
            collect_tactic_block_spans(tokens, open, close, tactics, spans)
        }
    }
}

fn direct_tactic_token_ranges(
    tokens: &[SourceToken],
    open: usize,
    close: usize,
) -> Result<Vec<Range<usize>>, ClickError> {
    let mut ranges = Vec::new();
    let mut start = open + 1;
    while start < close {
        let end = tactic_end_token(tokens, start, close)?;
        ranges.push(start..end + 1);
        start = end + 1;
    }
    Ok(ranges)
}

fn tactic_end_token(
    tokens: &[SourceToken],
    start: usize,
    close: usize,
) -> Result<usize, ClickError> {
    let mut cursor = start;
    let mut braces = 0_usize;
    let mut parentheses = 0_usize;
    let mut brackets = 0_usize;
    // Quantifiers in a `have` proposition own braces too. Only the block
    // after its top-level `by` can terminate the tactic.
    let mut have_body_started = tokens[start].text != "have";
    loop {
        if cursor >= close {
            return Err(ClickError::new(
                "unterminated tactic in selected source proof",
            ));
        }
        match tokens[cursor].text.as_str() {
            "by" if braces == 0 && parentheses == 0 && brackets == 0 => {
                have_body_started = true;
            }
            "{" => braces += 1,
            "}" => {
                braces = braces.checked_sub(1).ok_or_else(|| {
                    ClickError::new("unbalanced tactic block in selected source proof")
                })?;
                if have_body_started && braces == 0 && parentheses == 0 && brackets == 0 {
                    let continuation = tokens.get(cursor + 1).map(|token| token.text.as_str());
                    // A destructuring proof binding starts with a brace,
                    // but its `}` is followed by `=` rather than ending
                    // the tactic: `let { slot: child } = unfold(parent)`
                    // and `let { binder: instance } = step(...)`.
                    if !(matches!(continuation, Some("else" | "by" | "="))
                        || (tokens[start].text == "both" && continuation == Some("and"))
                        || (tokens[start].text == "match" && continuation == Some("{")))
                    {
                        let terminator = if continuation == Some(";") {
                            cursor + 1
                        } else {
                            cursor
                        };
                        return Ok(terminator);
                    }
                }
            }
            "(" => parentheses += 1,
            ")" => {
                parentheses = parentheses.checked_sub(1).ok_or_else(|| {
                    ClickError::new("unbalanced tactic call in selected source proof")
                })?;
            }
            "[" => brackets += 1,
            "]" => {
                brackets = brackets.checked_sub(1).ok_or_else(|| {
                    ClickError::new("unbalanced tactic index in selected source proof")
                })?;
            }
            ";" if braces == 0 && parentheses == 0 && brackets == 0 => return Ok(cursor),
            _ => {}
        }
        cursor += 1;
    }
}

fn find_if_branch_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
) -> Result<(usize, usize, usize, usize), ClickError> {
    let mut depth = 0_usize;
    let mut outer_open = None;
    let mut then_block = None;
    for cursor in tactic.start + 1..tactic.end {
        match tokens[cursor].text.as_str() {
            "{" => {
                if depth == 0 {
                    outer_open = Some(cursor);
                }
                depth += 1;
            }
            "}" => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| ClickError::new("unbalanced `if` tactic source block"))?;
                if depth == 0
                    && tokens.get(cursor + 1).map(|token| token.text.as_str()) == Some("else")
                {
                    then_block = outer_open.map(|open| (open, cursor));
                }
            }
            _ => {}
        }
    }
    let (then_open, then_close) =
        then_block.ok_or_else(|| ClickError::new("could not locate proof `if` then branch"))?;
    let else_keyword = then_close + 1;
    let else_open = else_keyword + 1;
    if tokens.get(else_open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new("could not locate proof `if` else branch"));
    }
    let else_close = matching_delimiter(tokens, else_open, "{", "}")?;
    Ok((then_open, then_close, else_open, else_close))
}

fn find_branch_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
) -> Result<(usize, usize, usize, usize), ClickError> {
    find_named_arm_blocks(tokens, tactic, "then", "else", "branch")
}

fn find_named_arm_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
    first: &str,
    second: &str,
    kind: &str,
) -> Result<(usize, usize, usize, usize), ClickError> {
    let outer_open = (tactic.start + 1..tactic.end)
        .find(|index| tokens[*index].text == "{")
        .ok_or_else(|| ClickError::new(format!("source `{kind}` tactic has no body")))?;
    let outer_close = matching_delimiter(tokens, outer_open, "{", "}")?;
    let find_named_block = |name: &str| -> Result<(usize, usize), ClickError> {
        let mut depth = 0_usize;
        for keyword in outer_open + 1..outer_close {
            match tokens[keyword].text.as_str() {
                "{" => depth += 1,
                "}" => depth = depth.saturating_sub(1),
                text if depth == 0
                    && text == name
                    && tokens.get(keyword + 1).map(|token| token.text.as_str()) == Some("{") =>
                {
                    let open = keyword + 1;
                    return Ok((open, matching_delimiter(tokens, open, "{", "}")?));
                }
                _ => {}
            }
        }
        Err(ClickError::new(format!(
            "could not locate `{kind}` {name} arm"
        )))
    };
    let (then_open, then_close) = find_named_block(first)?;
    let (else_open, else_close) = find_named_block(second)?;
    Ok((then_open, then_close, else_open, else_close))
}

fn find_structural_induction_arm_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
) -> Result<Vec<(usize, usize)>, ClickError> {
    // The scrutinee may itself contain match/let blocks. The proof arms are
    // the final block, not necessarily the first opening brace in the tactic.
    let outer_close = (tactic.start + 1..tactic.end)
        .rfind(|index| tokens[*index].text == "}")
        .ok_or_else(|| ClickError::new("source constructor tactic has no body"))?;
    let mut depth = 1_usize;
    let outer_open = (tactic.start + 1..outer_close)
        .rev()
        .find(|index| {
            match tokens[*index].text.as_str() {
                "}" => depth += 1,
                "{" => depth -= 1,
                _ => {}
            }
            depth == 0
        })
        .ok_or_else(|| ClickError::new("unbalanced constructor tactic body"))?;
    let mut blocks = Vec::new();
    let mut cursor = outer_open + 1;
    while cursor < outer_close {
        if tokens[cursor].text == "{" {
            let close = matching_delimiter(tokens, cursor, "{", "}")?;
            blocks.push((cursor, close));
            cursor = close + 1;
        } else {
            cursor += 1;
        }
    }
    Ok(blocks)
}

#[cfg(test)]
fn find_tactic_span(
    tokens: &[SourceToken],
    proof_span: &Range<usize>,
    wanted: usize,
) -> Result<Range<usize>, ClickError> {
    let by = tokens
        .iter()
        .position(|token| token.span.start == proof_span.start && token.text == "by")
        .ok_or_else(|| ClickError::new("could not locate selected source proof"))?;
    let open = by + 1;
    if tokens.get(open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new(
            "individual tactic expansion requires an explicit `by { ... }` proof",
        ));
    }
    let close = matching_delimiter(tokens, open, "{", "}")?;
    if let Some(range) = direct_tactic_token_ranges(tokens, open, close)?.get(wanted) {
        return Ok(tokens[range.start].span.start..tokens[range.end - 1].span.end);
    }
    Err(ClickError::new(format!(
        "selected source proof has no tactic {wanted}"
    )))
}

fn matching_delimiter(
    tokens: &[SourceToken],
    open: usize,
    opening: &str,
    closing: &str,
) -> Result<usize, ClickError> {
    let mut depth = 0;
    for (index, token) in tokens.iter().enumerate().skip(open) {
        if token.text == opening {
            depth += 1;
        } else if token.text == closing {
            depth -= 1;
            if depth == 0 {
                return Ok(index);
            }
        }
    }
    Err(ClickError::new(format!(
        "unterminated `{opening}` while locating proof source"
    )))
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
