use std::ops::Range;

use super::validation::tactic_name;
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CProofClaim {
    Ensure(usize),
    Effect(usize),
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
    let replacement = theorem.expanded_proof_source()?;
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

pub use crate::lang::SourcePosition;

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
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    let mut sites = Vec::new();
    for theorem in file.theorem_definitions() {
        for (ensure_index, ensure) in theorem.ensures().iter().enumerate() {
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
            let region_label = match clause.region() {
                CodeRegion::Function => format!("{function_name}.function"),
                CodeRegion::Loop(index) => format!("{function_name}.loop({index})"),
                CodeRegion::Statement(index) => format!("{function_name}.statement({index})"),
            };
            if let CodeRegion::Loop(loop_index) = clause.region() {
                let default = Proof::Default;
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
            for (item_index, item) in clause.items().iter().enumerate() {
                // Invariants have no independent source proof: their obligations
                // are certified by the loop's initialize and preserve proofs.
                if item.kind() == StructuralItemKind::Invariant {
                    continue;
                }
                let kind = match item.kind() {
                    StructuralItemKind::Invariant => unreachable!(),
                    StructuralItemKind::Assert => "assert",
                    StructuralItemKind::Effect => "effect",
                    StructuralItemKind::StepEffect => "step_effect",
                };
                collect_smart_proof_sites(
                    &format!("{region_label}.{kind}_{item_index}"),
                    item.proof(),
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
        for (index, effect) in function.effects().iter().enumerate() {
            let kind = match effect.effect() {
                Effect::Immutable => "immutable",
                Effect::Mutable(_) => "mutable",
            };
            collect_smart_proof_sites(
                &format!("{function_name}.{kind}_{index}"),
                effect.proof(),
                &mut sites,
            );
        }
    }
    Ok(sites)
}

fn collect_smart_proof_sites(
    claim_label: &str,
    proof: &Proof,
    sites: &mut Vec<SmartTacticSourceSite>,
) {
    match proof {
        Proof::Default => sites.push(SmartTacticSourceSite {
            claim_label: claim_label.to_string(),
            source_index: 0,
            tactic_name: "auto".to_string(),
        }),
        Proof::Tactic(tactic) => sites.push(SmartTacticSourceSite {
            claim_label: claim_label.to_string(),
            source_index: 0,
            tactic_name: match tactic {
                SmartTactic::Auto => "auto",
                SmartTactic::Frame => "frame",
                SmartTactic::Simp => "simp",
            }
            .to_string(),
        }),
        Proof::Script(tactics) => {
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
        if source_tactic_class(tactic) == SourceTacticClass::Smart {
            sites.push(SmartTacticSourceSite {
                claim_label: claim_label.to_string(),
                source_index,
                tactic_name: tactic_name(tactic).to_string(),
            });
        }
        match tactic {
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
            ProofTactic::Reach(advance) => {
                collect_smart_script_sites(claim_label, &advance.tactics, source_index + 1, sites)
            }
            _ => {}
        }
        source_index += source_tactic_count(std::slice::from_ref(tactic));
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum VerificationTarget {
    Function(String),
    Theorem(String),
}

pub(super) fn verification_target_at(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<VerificationTarget, ClickError> {
    let wanted = offset_at_position(click_source, line, column)?;
    let tokens = scan_source_tokens(click_source)?;
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    for theorem in file.theorem_definitions() {
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
    let selected = locate_source_tactic(click_source, c_sources, line, column)?;
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &selected.site
    {
        return expand_pure_theorem_source(click_source, c_sources, theorem_name, *ensure_index);
    }
    if let (
        ProofSite::FunctionClaim {
            function_name,
            claim,
        },
        TacticSourceEdit::WholeProof(_),
    ) = (&selected.site, &selected.edit)
    {
        return expand_c0_claim_source(click_source, c_sources, function_name, *claim);
    }
    let replacement_tactics = match &selected.edit {
        TacticSourceEdit::Partial(_) => super::proof::capture_c0_tactic_expansion(
            click_source,
            c_sources,
            selected.site.clone(),
            selected.source_index,
        )?,
        TacticSourceEdit::WholeProof(_) => super::proof::capture_c0_proof_site_expansion(
            click_source,
            c_sources,
            selected.site.clone(),
        )?,
    };
    let (span, replacement) = match selected.edit {
        TacticSourceEdit::Partial(span) => (
            span,
            super::printing::format_partial_tactic_sequence(&replacement_tactics),
        ),
        TacticSourceEdit::WholeProof(edit) => {
            let certificate =
                TacticCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: {error:?}"
                    ))
                })?;
            let replacement = super::printing::format_tactic_certificate(&certificate);
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
    Ok(expanded)
}

fn expand_pure_theorem_source(
    click_source: &str,
    c_sources: &[(&str, &str)],
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let verified = verify_click_theorems_with_c_sources(click_source, c_sources)?;
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
    let tokens = scan_source_tokens(click_source)?;
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
        CProofClaim::Effect(index) => verified.iter().find(|theorem| {
            matches_function(theorem)
                && matches!(theorem.claim, VerifiedClaim::Effect { index: found, .. } if found == index)
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
        if tokens
            .get(parameters_close + 1)
            .map(|token| token.text.as_str())
            != Some("{")
        {
            continue;
        }
        let body_open = parameters_close + 1;
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
            || tokens.get(index + 2).map(|token| token.text.as_str()) != Some("(")
        {
            continue;
        }
        let parameters_close = matching_delimiter(tokens, index + 2, "(", ")")?;
        if tokens
            .get(parameters_close + 1)
            .map(|token| token.text.as_str())
            != Some("{")
        {
            continue;
        }
        let body_open = parameters_close + 1;
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
            "ensures" | "owns" | "produces" if depth == 0 => {
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
    if let CProofClaim::Ensure(index) = claim {
        return find_ensure_proof_edit(tokens, function.body_open, function.body_close, index);
    }
    let (keyword, wanted) = match claim {
        CProofClaim::Ensure(_) => unreachable!(),
        CProofClaim::Effect(index) => ("effect", index),
        CProofClaim::Grouped => unreachable!(),
    };
    let mut depth = 0;
    let mut found = 0;
    let mut index = function.body_open + 1;
    while index < function.body_close {
        match tokens[index].text.as_str() {
            "{" => depth += 1,
            "}" => depth -= 1,
            text if depth == 0
                && (text == keyword
                    || keyword == "effect" && matches!(text, "immutable" | "mutable")) =>
            {
                if found == wanted {
                    let mut cursor = index + 1;
                    let mut nested = 0;
                    while cursor < function.body_close {
                        match tokens[cursor].text.as_str() {
                            "{" | "(" | "[" => nested += 1,
                            "}" | ")" | "]" => nested -= 1,
                            "by" if nested == 0 => {
                                return Ok(ProofSourceEdit::Explicit(proof_span(tokens, cursor)?));
                            }
                            ";" if nested == 0 => {
                                return Ok(ProofSourceEdit::DefaultTerminator {
                                    span: tokens[cursor].span.clone(),
                                    selector: tokens[index].span.start,
                                });
                            }
                            _ => {}
                        }
                        cursor += 1;
                    }
                }
                found += 1;
            }
            _ => {}
        }
        index += 1;
    }
    Err(ClickError::new(format!(
        "could not locate source clause for {claim:?}"
    )))
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
    StructuralItem {
        function_name: String,
        region: CodeRegion,
        item_index: usize,
        kind: StructuralItemKind,
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
            Self::StructuralItem {
                function_name,
                region,
                item_index,
                kind,
            } => {
                let region = match region {
                    CodeRegion::Function => "function".to_string(),
                    CodeRegion::Loop(index) => format!("loop({index})"),
                    CodeRegion::Statement(index) => format!("statement({index})"),
                };
                let kind = match kind {
                    StructuralItemKind::Invariant => "invariant",
                    StructuralItemKind::Assert => "assert",
                    StructuralItemKind::Effect => "effect",
                    StructuralItemKind::StepEffect => "step_effect",
                };
                format!("{function_name}.{region}.{kind}_{item_index}")
            }
        }
    }
}

#[derive(Clone, Debug)]
enum TacticSourceEdit {
    Partial(Range<usize>),
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
    let wanted = offset_at_position(click_source, line, column)?;
    let tokens = scan_source_tokens(click_source)?;
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    for theorem in file.theorem_definitions() {
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
                    let default_proof = Proof::Default;
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
            for (item_index, (item, edit)) in clause.items().iter().zip(edits.iter()).enumerate() {
                if let Some(found) = locate_tactic_in_proof(
                    &tokens,
                    edit,
                    item.proof(),
                    wanted,
                    ProofSite::StructuralItem {
                        function_name: function_name.to_string(),
                        region: *clause.region(),
                        item_index,
                        kind: item.kind(),
                    },
                )? {
                    return Ok(found);
                }
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
        for (index, effect) in function_block.effects().iter().enumerate() {
            let claim = CProofClaim::Effect(index);
            let edit = find_claim_proof_edit(&tokens, &function, claim)?;
            if let Some(found) = locate_tactic_in_proof(
                &tokens,
                &edit,
                effect.proof(),
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

fn locate_tactic_in_proof(
    tokens: &[SourceToken],
    edit: &ProofSourceEdit,
    proof: &Proof,
    wanted: usize,
    site: ProofSite,
) -> Result<Option<LocatedSourceTactic>, ClickError> {
    match proof {
        Proof::Script(tactics) => {
            let ProofSourceEdit::Explicit(proof_span) = edit else {
                return Err(ClickError::new(
                    "an explicit proof script has no source `by` clause",
                ));
            };
            let spans = collect_source_tactic_spans(tokens, proof_span, tactics)?;
            Ok(spans
                .into_iter()
                .enumerate()
                .find(|(_, span)| span.start == wanted)
                .map(|(source_index, span)| LocatedSourceTactic {
                    site,
                    source_index,
                    edit: TacticSourceEdit::Partial(span),
                }))
        }
        Proof::Tactic(_) => match edit {
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
        Proof::Default => Ok((edit.selector() == wanted).then(|| LocatedSourceTactic {
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
    let tokens = scan_source_tokens(click_source)?;
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    for theorem in file.theorem_definitions() {
        let source = find_theorem(&tokens, theorem.name())?;
        for (ensure_index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{ensure_index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            if label != claim_label {
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
            let region_label = match clause.region() {
                CodeRegion::Function => format!("{function_name}.function"),
                CodeRegion::Loop(index) => format!("{function_name}.loop({index})"),
                CodeRegion::Statement(index) => format!("{function_name}.statement({index})"),
            };
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
            for (item_index, (item, edit)) in clause.items().iter().zip(edits.iter()).enumerate() {
                let kind = match item.kind() {
                    StructuralItemKind::Invariant => "invariant",
                    StructuralItemKind::Assert => "assert",
                    StructuralItemKind::Effect => "effect",
                    StructuralItemKind::StepEffect => "step_effect",
                };
                if claim_label != format!("{region_label}.{kind}_{item_index}") {
                    continue;
                }
                return proof_source_position(
                    click_source,
                    &tokens,
                    match edit {
                        ProofSourceEdit::Explicit(span) => Some(span),
                        ProofSourceEdit::DefaultTerminator { .. }
                        | ProofSourceEdit::OmittedLoopPhase { .. } => None,
                    },
                    Some(item.proof()),
                    edit.selector(),
                    claim_label,
                    source_index,
                );
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
                        .effects()
                        .iter()
                        .enumerate()
                        .find_map(|(index, effect)| {
                            let kind = match effect.effect() {
                                Effect::Immutable => "immutable",
                                Effect::Mutable(_) => "mutable",
                            };
                            (claim_label == format!("{function_name}.{kind}_{index}"))
                                .then_some((CProofClaim::Effect(index), effect.proof()))
                        })
                })
        };
        let Some((claim, proof)) = selected else {
            continue;
        };
        let fallback = match claim {
            CProofClaim::Grouped => tokens[function.body_close].span.start,
            CProofClaim::Ensure(_) | CProofClaim::Effect(_) => {
                find_claim_clause_offset(&tokens, &function, claim)?
            }
        };
        let proof_span = match claim {
            CProofClaim::Grouped => Some(find_grouped_proof_span(&tokens, &function)?),
            CProofClaim::Ensure(_) | CProofClaim::Effect(_) => {
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
    proof: Option<&Proof>,
    fallback: usize,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    if let Some(tactics) = proof.and_then(Proof::tactics) {
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
    if let CProofClaim::Ensure(index) = claim {
        return Ok(
            find_ensure_proof_edit(tokens, function.body_open, function.body_close, index)?
                .selector(),
        );
    }
    let (keyword, wanted) = match claim {
        CProofClaim::Ensure(_) => unreachable!(),
        CProofClaim::Effect(index) => ("effect", index),
        CProofClaim::Grouped => unreachable!(),
    };
    let mut depth = 0;
    let mut found = 0;
    for token in &tokens[function.body_open + 1..function.body_close] {
        match token.text.as_str() {
            "{" => depth += 1,
            "}" => depth -= 1,
            text if depth == 0
                && (text == keyword
                    || keyword == "effect" && matches!(text, "immutable" | "mutable")) =>
            {
                if found == wanted {
                    return Ok(token.span.start);
                }
                found += 1;
            }
            _ => {}
        }
    }
    Err(ClickError::new(format!(
        "could not locate source clause for {claim:?}"
    )))
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
    let sources = c_sources.iter().copied().collect::<BTreeMap<_, _>>();
    let layouts = parse_c_struct_layouts(&sources)?;
    parser::parse_with_struct_layouts(click_source, layouts)
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

pub(super) fn position_at_offset(source: &str, offset: usize) -> SourcePosition {
    let prefix = &source[..offset];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let line_start = prefix.rfind('\n').map_or(0, |newline| newline + 1);
    let column = source[line_start..offset].chars().count() + 1;
    SourcePosition { line, column }
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
            ProofTactic::Reach(advance) => {
                let (body_open, body_close) = find_advance_body(tokens, &token_range)?;
                collect_tactic_block_spans(tokens, body_open, body_close, &advance.tactics, spans)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn direct_tactic_token_ranges(
    tokens: &[SourceToken],
    open: usize,
    close: usize,
) -> Result<Vec<Range<usize>>, ClickError> {
    let mut ranges = Vec::new();
    let mut start = open + 1;
    while start < close {
        let mut cursor = start;
        let mut braces = 0_usize;
        let mut parentheses = 0_usize;
        let mut brackets = 0_usize;
        let end = loop {
            if cursor >= close {
                return Err(ClickError::new(
                    "unterminated tactic in selected source proof",
                ));
            }
            match tokens[cursor].text.as_str() {
                "{" => braces += 1,
                "}" => {
                    braces = braces.checked_sub(1).ok_or_else(|| {
                        ClickError::new("unbalanced tactic block in selected source proof")
                    })?;
                    if braces == 0 && parentheses == 0 && brackets == 0 {
                        let continuation = tokens.get(cursor + 1).map(|token| token.text.as_str());
                        if !matches!(continuation, Some("else" | "by")) {
                            break cursor;
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
                ";" if braces == 0 && parentheses == 0 && brackets == 0 => break cursor,
                _ => {}
            }
            cursor += 1;
        };
        ranges.push(start..end + 1);
        start = end + 1;
    }
    Ok(ranges)
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

fn find_advance_body(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
) -> Result<(usize, usize), ClickError> {
    let mut depth = 0_usize;
    for cursor in tactic.start + 1..tactic.end {
        match tokens[cursor].text.as_str() {
            "{" => depth += 1,
            "}" => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| ClickError::new("unbalanced `reach` tactic source block"))?
            }
            "by" if depth == 0
                && tokens.get(cursor + 1).map(|token| token.text.as_str()) == Some("{") =>
            {
                let open = cursor + 1;
                return Ok((open, matching_delimiter(tokens, open, "{", "}")?));
            }
            _ => {}
        }
    }
    Err(ClickError::new("could not locate `reach` proof body"))
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
mod tests {
    use super::*;

    fn expand_top_level_tactic_for_test(
        click_source: &str,
        c_sources: &[(&str, &str)],
        function_name: &str,
        claim: CProofClaim,
        tactic_index: usize,
    ) -> Result<String, ClickError> {
        let tokens = scan_source_tokens(click_source)?;
        let function = find_function(&tokens, function_name)?;
        let proof = match claim {
            CProofClaim::Grouped => find_grouped_proof_span(&tokens, &function)?,
            CProofClaim::Ensure(_) | CProofClaim::Effect(_) => {
                find_claim_proof_span(&tokens, &function, claim)?
            }
        };
        let span = find_tactic_span(&tokens, &proof, tactic_index)?;
        let position = position_at_offset(click_source, span.start);
        expand_c0_tactic_source_at(click_source, c_sources, position.line, position.column)
    }

    #[test]
    fn expands_one_grouped_tactic_without_running_the_suffix() {
        let c_source = "int32 identity(int32 x) { return x; }";
        let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}
"#;

        let expanded = expand_top_level_tactic_for_test(
            click_source,
            &[("identity.c", c_source)],
            "identity",
            CProofClaim::Grouped,
            0,
        )
        .expect("the first grouped tactic should expand");

        assert!(!expanded.contains("execute();"));
        assert!(expanded.contains("    step() using {\n    }\n    simp();"));
        verify_c0_sources(&expanded, &[("identity.c", c_source)])
            .expect("the source with one expanded tactic should re-verify");
    }

    #[test]
    fn expands_grouped_immutable_read_with_multiple_claim_successors() {
        let c_source = "int32 read_first(int32 p[1]) { return p[0]; }";
        let click_source = r#"
verifying "read.c";

int32 read_first(int32 p[1]) {
    views p[0..1];
    immutable;
    ensures result == p[0];
} by {
    execute();
    frame();
    simp();
}
"#;

        let expanded = expand_top_level_tactic_for_test(
            click_source,
            &[("read.c", c_source)],
            "read_first",
            CProofClaim::Grouped,
            0,
        )
        .expect("the grouped immutable read should have one common expansion");

        assert!(!expanded.contains("execute();"));
        assert!(expanded.contains("step() using {"), "{expanded}");
        verify_c0_sources(&expanded, &[("read.c", c_source)])
            .expect("the expanded immutable read should re-verify every grouped claim");
    }

    #[test]
    fn expands_nested_branch_tactic_by_source_location() {
        let c_source = "int32 identity(int32 x) { return x; }";
        let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
} by {
    if x == x {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}
"#;
        let then_offset = click_source
            .find("        execute();")
            .expect("then tactic should exist")
            + 8;
        let position = position_at_offset(click_source, then_offset);
        let expanded = expand_c0_tactic_source_at(
            click_source,
            &[("identity.c", c_source)],
            position.line,
            position.column,
        )
        .expect("the nested then tactic should expand");

        assert_eq!(expanded.matches("execute();").count(), 1);
        assert!(
            expanded.contains("    if x == x {\n        step() using {"),
            "{expanded}"
        );
        verify_c0_sources(&expanded, &[("identity.c", c_source)])
            .expect("the source with one nested expansion should re-verify");
    }

    #[test]
    fn locates_a_block_tactic_as_one_source_statement() {
        let source = "by { have x == x by simp; simp(); }";
        let tokens = scan_source_tokens(source).expect("source should scan");
        let proof = proof_span(&tokens, 0).expect("proof should have a span");

        let first = find_tactic_span(&tokens, &proof, 0).expect("first tactic should exist");
        let second = find_tactic_span(&tokens, &proof, 1).expect("second tactic should exist");

        assert_eq!(&source[first], "have x == x by simp;");
        assert_eq!(&source[second], "simp();");
    }

    #[test]
    fn hides_statement_local_opaque_call_facts_from_surface_premises() {
        let zero_c = "int32 zero() { return 0; }";
        let caller_c = "int32 caller() { int32 value; value = zero(); return value; }";
        let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
        let sources = [("zero.c", zero_c), ("caller.c", caller_c)];

        let expanded = expand_top_level_tactic_for_test(
            click_source,
            &sources,
            "caller",
            CProofClaim::Grouped,
            0,
        )
        .expect("opaque call internals should not become surface premises");

        assert_eq!(expanded.matches("execute();").count(), 1);
        verify_c0_sources(&expanded, &sources)
            .expect("the caller with one expanded tactic should re-verify");
    }

    #[test]
    fn expands_public_opaque_call_results_through_later_call_arguments() {
        let zero_c = "int32 zero() { return 0; }";
        let passthrough_c = "int32 passthrough(int32 x) { return x; }";
        let caller_c = r#"int32 caller() {
    int32 first;
    int32 second;
    first = zero();
    second = passthrough(first);
    return second;
}"#;
        let click_source = r#"
verifying "zero.c";
verifying "passthrough.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 passthrough(int32 x) {
    ensures result == x;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
        let sources = [
            ("zero.c", zero_c),
            ("passthrough.c", passthrough_c),
            ("caller.c", caller_c),
        ];
        let final_simp = click_source
            .rfind("simp();")
            .expect("caller final simp should exist");
        let position = position_at_offset(click_source, final_simp);

        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
                .expect("public call facts should compose through their receiving locals");

        assert!(expanded.contains("first"), "{expanded}");
        assert!(expanded.contains("second"), "{expanded}");
        assert!(!expanded.contains("call-havoc"), "{expanded}");
        assert!(!expanded.contains("symbolic-pointer"), "{expanded}");
        verify_c0_sources(&expanded, &sources)
            .expect("the expanded public fact chain should independently re-verify");
    }

    #[test]
    fn grouped_simp_distinguishes_c_local_result_from_contract_result() {
        let zero_c = "int32 zero() { return 0; }";
        let caller_c = "int32 caller() { int32 result; result = zero(); return result; }";
        let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
        let sources = [("zero.c", zero_c), ("caller.c", caller_c)];
        let final_simp = click_source
            .rfind("simp();")
            .expect("caller final simp should exist");
        let position = position_at_offset(click_source, final_simp);

        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
                .expect("the grouped simp should expand across the local result assignment");

        verify_c0_sources(&expanded, &sources)
            .expect("the explicit C result binding should replay without aliasing contract result");

        let explicit_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute();
    have at(statement(2).entry, c(result)) == 0 by {
        assumption();
    }
    have result == at(statement(2).entry, c(result)) by {
        normalize();
    }
    assumption();
}
"#;
        verify_c0_sources(explicit_source, &sources)
            .expect("`c(result)` should denote the C local rather than contract result");
    }

    #[test]
    fn selected_tactic_emits_before_the_normal_verifier_checks_the_suffix() {
        let zero_c = "int32 zero() { return 1; }";
        let caller_c = "int32 caller() { int32 value; value = zero(); return value; }";
        let click_source = r#"
verifying "zero.c";
verifying "caller.c";

int32 zero() {
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    step();
    execute();
    simp();
}
"#;
        let sources = [("zero.c", zero_c), ("caller.c", caller_c)];

        let expanded = expand_top_level_tactic_for_test(
            click_source,
            &sources,
            "caller",
            CProofClaim::Grouped,
            0,
        )
        .expect("capture should emit without running the ordinary full verifier");

        let error = verify_c0_sources(&expanded, &sources)
            .expect_err("the separate verification step should reject the invalid sidecar");
        assert!(error.message().contains("zero.ensures_0"));
        assert!(
            error
                .message()
                .contains("grouped `simp` could not certify its complete claim transition")
        );
    }

    #[test]
    fn grouped_simp_expansion_preserves_each_claim_closer() {
        let c_source = "int32 identity(int32 x) { return x; }";
        let click_source = r#"
verifying "identity.c";

int32 identity(int32 x) {
    ensures result == x;
    ensures result == old(x);
} by {
    execute();
    simp();
}
"#;
        let sources = [("identity.c", c_source)];

        let expanded = expand_top_level_tactic_for_test(
            click_source,
            &sources,
            "identity",
            CProofClaim::Grouped,
            1,
        )
        .expect("grouped simp should expand");

        assert_eq!(expanded.matches("assumption();").count(), 2);
        verify_c0_sources(&expanded, &sources)
            .expect("each grouped claim closer should survive expansion");
    }

    #[test]
    fn grouped_simp_expansion_preserves_resource_scalar_and_quantified_transitions() {
        let c_source = "int32 inspect(int32 p[1], int32 x) { return 0; }";
        let click_source = r#"
verifying "inspect.c";

int32 inspect(int32 p[1], int32 x) {
    requires forall (k: int32) {
        0 <= k and k < 1 implies x == x
    };
    owns p[0..1];
    immutable;
    ensures result == 0;
    ensures forall (k: int32) {
        0 <= k and k < 1 implies x == x
    };
} by {
    execute();
    frame();
    simp();
}
"#;
        let sources = [("inspect.c", c_source)];

        let expanded = expand_top_level_tactic_for_test(
            click_source,
            &sources,
            "inspect",
            CProofClaim::Grouped,
            2,
        )
        .expect("grouped simp should capture every newly closed claim");

        assert!(!expanded.contains("simp();"), "{expanded}");
        verify_c0_sources(&expanded, &sources)
            .expect("the grouped transition certificate should re-verify");
    }

    #[test]
    fn grouped_simp_expansion_uses_explicit_frame_consequences() {
        let c_source = r#"
int32 increment_and_return_old(int32 p[1]) {
    int32 result;
    result = p[0];
    p[0] = 0;
    return result;
}
"#;
        let click_source = r#"
verifying "increment.c";

int32 increment_and_return_old(int32 p[1]) {
    owns p[0..1];
    mutable p[0..1];
    ensures result == old(p[0]);
    ensures p[0] == 0;
} by {
    execute();
    frame();
    simp();
}
"#;
        let sources = [("increment.c", c_source)];

        let expanded = expand_top_level_tactic_for_test(
            click_source,
            &sources,
            "increment_and_return_old",
            CProofClaim::Grouped,
            2,
        )
        .expect("grouped simp should capture frame-dependent claims");

        assert!(!expanded.contains("simp();"), "{expanded}");
        verify_c0_sources(&expanded, &sources)
            .expect("the grouped frame transition certificate should re-verify");
    }

    #[test]
    fn expansion_preserves_unfolded_resource_and_predicate_fact_spellings() {
        let c_source = r#"
struct box {
    int32 len;
    int32 cap;
    int32* data;
};

int32 inspect(struct box* owner) {
    int32 ignored;
    return 0;
}
"#;
        let click_source = r#"
predicate terminated_at(data: int32[], length: int32) {
    data[length] == 0
}

resource owned_box(owner: struct box*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(object(owner)),
        memory(owner->data[0..owner->cap])
    );
}

verifying "inspect.c";

int32 inspect(struct box* owner) {
    consumes owned_box(owner);
    ensures result == 0;
} by {
    unfold(owned_box(owner));
    unfold(terminated_at);
    step();
    execute();
    simp();
}
"#;

        let expanded = expand_top_level_tactic_for_test(
            click_source,
            &[("inspect.c", c_source)],
            "inspect",
            CProofClaim::Grouped,
            2,
        )
        .expect("the declaration should expand with unfolded surface facts");

        // The assertions below are about the emitted `step() using` premises,
        // not the resource declaration echoed above them; scope to the block
        // so a spelling surviving only in the declaration cannot pass.
        let step_using = expanded
            .split("step() using {")
            .nth(1)
            .and_then(|rest| rest.split_once('}'))
            .map(|(block, _)| block)
            .expect("the expansion should emit a step() using block");
        assert!(
            step_using
                .contains("separate(memory(object(owner)), memory(owner->data[0..owner->cap]));"),
            "{expanded}"
        );
        // The aggregate premise replaces its per-field decomposition.
        assert!(
            !step_using.contains("memory(owner->len), memory(owner->data["),
            "{expanded}"
        );
        assert!(
            !step_using.contains("memory(owner->cap), memory(owner->data["),
            "{expanded}"
        );
        assert!(
            !step_using.contains("memory(owner->data), memory(owner->data["),
            "{expanded}"
        );
        // The proof unfolds `terminated_at`, so the premise carries the
        // unfolded predicate body's canonical spelling, and only the resource
        // declaration keeps the folded call spelling.
        assert!(
            step_using.contains("owner->data[owner->len] == 0;"),
            "{expanded}"
        );
        assert!(!step_using.contains("terminated_at"), "{expanded}");
        assert!(
            expanded.contains("fact terminated_at(owner->data, owner->len);"),
            "{expanded}"
        );
        verify_c0_sources(&expanded, &[("inspect.c", c_source)])
            .expect("the re-folded aggregate premise should re-verify");
    }

    #[test]
    fn source_position_maps_smart_and_implicit_default_proofs() {
        let c_source = "int32 identity(int32 x) { return x; }";
        let explicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
} by auto;
"#;
        assert_eq!(
            c0_tactic_source_position(
                explicit,
                &[("identity.c", c_source)],
                "identity.contract",
                0,
            )
            .unwrap(),
            SourcePosition { line: 4, column: 6 }
        );
        assert!(
            c0_tactic_source_position(
                explicit,
                &[("identity.c", c_source)],
                "identity.contract",
                2,
            )
            .is_err()
        );
        let expanded = expand_c0_tactic_source_at(explicit, &[("identity.c", c_source)], 4, 6)
            .expect("an internal smart-proof timing should select the whole source proof");
        assert!(!expanded.contains("by auto"));
        verify_c0_sources(&expanded, &[("identity.c", c_source)])
            .expect("the expanded smart proof should verify");

        let implicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
        assert_eq!(
            c0_tactic_source_position(
                implicit,
                &[("identity.c", c_source)],
                "identity.ensures_0",
                0,
            )
            .unwrap(),
            SourcePosition { line: 3, column: 5 }
        );
        assert!(
            c0_tactic_source_position(
                implicit,
                &[("identity.c", c_source)],
                "identity.ensures_0",
                2,
            )
            .is_err()
        );
    }

    #[test]
    fn source_position_maps_loop_phase_proofs() {
        let c_source = "int32 count(int32 n) { while (n > 0) { n = n - 1; } return n; }";
        let click_source = r#"verifying "count.c";
int32 count(int32 n) {
    for loop(0) as countdown {
        invariant n == n;
        initialize by simp;
        preserve by {
            step();
            simp();
        }
    }
    ensures result == result;
}
"#;
        assert_eq!(
            c0_tactic_source_position(
                click_source,
                &[("count.c", c_source)],
                "count.loop(0).initialize",
                0,
            )
            .unwrap(),
            SourcePosition {
                line: 5,
                column: 23
            }
        );
        assert_eq!(
            c0_tactic_source_position(
                click_source,
                &[("count.c", c_source)],
                "count.loop(0).preserve",
                0,
            )
            .unwrap(),
            SourcePosition {
                line: 7,
                column: 13
            }
        );
        let preserve_position = SourcePosition {
            line: 7,
            column: 13,
        };
        let expanded = expand_c0_tactic_source_at(
            click_source,
            &[("count.c", c_source)],
            preserve_position.line,
            preserve_position.column,
        )
        .expect("a smart tactic inside loop preservation should expand");
        assert!(!expanded.contains("step();"));
        verify_c0_sources(&expanded, &[("count.c", c_source)]).unwrap_or_else(|error| {
            panic!(
                "expanded loop-preservation tactic should re-verify: {}\n{expanded}",
                error.message()
            )
        });
    }

    #[test]
    fn source_selection_recognizes_theorem_loop_and_structural_proofs() {
        let theorem_source = r#"theorem reflexive(x: int32) {
    ensures same: x == x by simp;
}
"#;
        let theorem_offset = theorem_source.find("simp").unwrap();
        let theorem_position = position_at_offset(theorem_source, theorem_offset);
        assert_eq!(
            c0_tactic_source_position(theorem_source, &[], "reflexive.same", 0).unwrap(),
            theorem_position
        );
        let theorem_expanded = expand_c0_tactic_source_at(
            theorem_source,
            &[],
            theorem_position.line,
            theorem_position.column,
        )
        .expect("theorem smart proof should expand through its certificate");
        assert!(!theorem_expanded.contains("simp"));
        verify_click_theorems(&theorem_expanded).expect("expanded theorem should re-verify");

        let c_source = "int32 count(int32 n) { while (n > 0) { n = n - 1; } return n; }";
        let click_source = r#"verifying "count.c";
int32 count(int32 n) {
    for loop(0) {
        invariant n == n;
        assert n == n by auto;
        initialize by simp;
        preserve by simp;
    }
    ensures result == result;
}
"#;
        for needle in [
            "initialize by simp",
            "preserve by simp",
            "assert n == n by auto",
        ] {
            let offset = click_source.find(needle).unwrap()
                + if needle.starts_with("assert") {
                    needle.find("auto").unwrap()
                } else {
                    needle.find("simp").unwrap()
                };
            let position = position_at_offset(click_source, offset);
            let expanded = expand_c0_tactic_source_at(
                click_source,
                &[("count.c", c_source)],
                position.line,
                position.column,
            )
            .expect("the selected proof site should expand through its retained certificate");
            verify_c0_sources(&expanded, &[("count.c", c_source)])
                .expect("the rewritten proof site should re-verify");
        }
        let assert_offset =
            click_source.find("assert n == n by auto").unwrap() + "assert n == n by ".len();
        assert_eq!(
            c0_tactic_source_position(
                click_source,
                &[("count.c", c_source)],
                "count.loop(0).assert_1",
                0,
            )
            .unwrap(),
            position_at_offset(click_source, assert_offset)
        );
    }

    #[test]
    fn expands_whole_and_step_structural_effect_certificates() {
        let c_source = "int32 count(int32 n) { while (n > 0) { n = n - 1; } return n; }";
        let click_source = r#"verifying "count.c";
int32 count(int32 n) {
    for loop(0) {
        invariant n == n;
        immutable by auto;
        step {
            immutable by frame;
        }
    }
    ensures result == result;
}
"#;
        for needle in ["immutable by auto", "immutable by frame"] {
            let tactic = if needle.ends_with("auto") {
                "auto"
            } else {
                "frame"
            };
            let offset = click_source.find(needle).unwrap() + needle.find(tactic).unwrap();
            let position = position_at_offset(click_source, offset);
            let expanded = expand_c0_tactic_source_at(
                click_source,
                &[("count.c", c_source)],
                position.line,
                position.column,
            )
            .expect("structural effect smart proof should expand");
            assert!(expanded.contains("immutable by {\n"));
            assert!(expanded.contains("frame() using {"));
            verify_c0_sources(&expanded, &[("count.c", c_source)])
                .expect("expanded structural effect certificate should re-verify");
        }

        let omitted = r#"verifying "count.c";
int32 count(int32 n) {
    for loop(0) {
        invariant n == n;
        immutable;
    }
    ensures result == result;
}
"#;
        let position = c0_tactic_source_position(
            omitted,
            &[("count.c", c_source)],
            "count.loop(0).effect_1",
            0,
        )
        .expect("omitted structural effect should have a source coordinate");
        let expanded = expand_c0_tactic_source_at(
            omitted,
            &[("count.c", c_source)],
            position.line,
            position.column,
        )
        .expect("omitted structural effect should expand");
        assert!(expanded.contains("immutable by {\n"));
        verify_c0_sources(&expanded, &[("count.c", c_source)])
            .expect("expanded omitted structural effect should re-verify");
    }

    #[test]
    fn expands_smart_tactics_inside_loop_initialization_and_structural_assertions() {
        let c_source = "int32 count(int32 n) { while (n > 0) { n = n - 1; } return n; }";
        let click_source = r#"verifying "count.c";
int32 count(int32 n) {
    for loop(0) {
        invariant n == n;
        invariant n == n;
        assert n == n by {
            simp();
        }
        initialize by {
            simp();
        }
        preserve by auto;
    }
    ensures result == result;
}
"#;
        for needle in [
            "assert n == n by {\n            simp",
            "initialize by {\n            simp",
        ] {
            let offset = click_source.find(needle).unwrap() + needle.rfind("simp").unwrap();
            let position = position_at_offset(click_source, offset);
            let expanded = expand_c0_tactic_source_at(
                click_source,
                &[("count.c", c_source)],
                position.line,
                position.column,
            )
            .expect("point-pure smart tactic should expand at its source location");
            assert_eq!(expanded.matches("simp();").count(), 1);
            verify_c0_sources(&expanded, &[("count.c", c_source)]).unwrap_or_else(|error| {
                panic!(
                    "expanded point-pure tactic should re-verify: {}\n{expanded}",
                    error.message()
                )
            });
        }
    }

    #[test]
    fn expands_shared_loop_initialization_simp_to_a_replayable_certificate() {
        let c_source = r#"int32 bubble_pass3(int32 p[3]) {
    int32 j;
    int32 tmp;
    j = 0;
    while (j < 2) {
        if (p[j + 1] < p[j]) {
            tmp = p[j];
            p[j] = p[j + 1];
            p[j + 1] = tmp;
        }
        j = j + 1;
    }
    return 0;
}"#;
        let click_source = r#"verifying "bubble_pass3.c";
predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
    forall (k: int32) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}
int32 bubble_pass3(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    for loop(0) {
        invariant j >= 0 and j <= 2;
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            unfold(all_le_range);
            simp();
        }
        preserve by {
            unfold(all_le_range);
        }
        mutable p[0..3] by frame;
    }
    ensures all_le_range(p, 0, 2, p[2]) by {
        execute();
        unfold(all_le_range);
        simp();
    }
}"#;
        let offset = click_source
            .find("initialize by")
            .and_then(|start| {
                click_source[start..]
                    .find("simp")
                    .map(|offset| start + offset)
            })
            .expect("initialization simp should have a source position");
        let position = position_at_offset(click_source, offset);
        let expanded = expand_c0_tactic_source_at(
            click_source,
            &[("bubble_pass3.c", c_source)],
            position.line,
            position.column,
        )
        .expect("shared initialization simp should expand");

        assert!(expanded.contains("have j >= 0 and j <= 2 by"));
        assert!(expanded.contains("have all_le_range(p, 0, j, p[j]) by"));
        verify_c0_sources(&expanded, &[("bubble_pass3.c", c_source)])
            .expect("expanded shared initialization certificate should re-verify");
    }

    #[test]
    fn expands_loop_initialization_loads_using_conjoined_bounds() {
        let c_source = r#"int32 fill_tail_keeps_first(int32 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}"#;
        let click_source = r#"verifying "fill_tail_keeps_first.c";
int32 fill_tail_keeps_first(int32 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    requires loadable(p[0..n]);
    consumes p[0..n];
    for loop(0) {
        invariant i >= 1 and i <= n;
        invariant p[0] == old(p[0]);
    }
    ensures p[0] == old(p[0]) and result == n by auto;
}"#;
        let sources = [("fill_tail_keeps_first.c", c_source)];
        let position = c0_tactic_source_position(
            click_source,
            &sources,
            "fill_tail_keeps_first.loop(0).initialize",
            0,
        )
        .expect("omitted initialization should have a selector");
        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
                .expect("initialization proof should expand");

        assert!(expanded.contains("have p[0] == old(p[0]) by"));
        verify_c0_sources(&expanded, &sources)
            .expect("conjoined bounds should remain available while lowering the load");
    }

    #[test]
    fn expands_each_smart_tactic_in_an_explicit_loop_initialization() {
        let c_source = r#"int32 count_up(int32 x) {
    while (x < 1) {
        x = 0;
    }
    return x;
}"#;
        let click_source = r#"verifying "count_up.c";
predicate acceptable(x: int32) {
    x >= 0
}
theorem nonnegative_is_acceptable(x: int32) {
    requires x >= 0;
    ensures acceptable(x) by {
        unfold(acceptable);
        simp();
    }
}
int32 count_up(int32 x) {
    requires x >= 0;
    for loop(0) {
        invariant acceptable(x);
        initialize by {
            apply(nonnegative_is_acceptable(x));
            simp();
        }
        preserve by {
            step();
            apply(nonnegative_is_acceptable(x));
            simp();
        }
    }
    ensures acceptable(result) by {
        execute();
        unfold(acceptable);
        simp();
    }
}"#;
        let sources = [("count_up.c", c_source)];
        let initialize = click_source.find("initialize by").unwrap();
        for needle in ["apply", "simp"] {
            let offset = initialize
                + click_source[initialize..]
                    .find(needle)
                    .expect("initialization tactic should be present");
            let position = position_at_offset(click_source, offset);
            let expanded =
                expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
                    .expect("initialization tactic should expand");
            verify_c0_sources(&expanded, &sources)
                .expect("expanded initialization tactic should re-verify");
        }
    }

    #[test]
    fn expanded_uint8_facts_print_as_parseable_typed_literals() {
        let c_source = "int32 contains(uint8 p[], int32 n) { return 0; }";
        let click_source = r#"verifying "contains.c";
int32 contains(uint8 p[], int32 n) {
    requires loadable(p[0..n]);
    requires has_x: bytes_contains(p, 0, n, 'x');
    ensures bytes_contains(p, 0, n, 'x') by {
        execute();
        unfold(bytes_contains);
        choose(found from requirement has_x);
        witness(k = found);
        simp();
    }
}"#;
        let offset = click_source.rfind("simp").expect("simp should be present");
        let position = position_at_offset(click_source, offset);
        let expanded = expand_c0_tactic_source_at(
            click_source,
            &[("contains.c", c_source)],
            position.line,
            position.column,
        )
        .expect("uint8 proposition should expand");

        assert!(expanded.contains("bytes_contains(p, 0, n, 120u8)"));
        verify_c0_sources(&expanded, &[("contains.c", c_source)])
            .expect("printed uint8 literal should parse and re-verify");
    }

    #[test]
    fn expanded_bitvector_facts_print_parseable_negative_literals() {
        let c_source = "int32 all_bits() { return ~0; }";
        let click_source = r#"verifying "all_bits.c";
int32 all_bits() {
    ensures result == 4294967295 by auto;
}"#;
        let offset = click_source.find("auto").expect("auto should be present");
        let position = position_at_offset(click_source, offset);
        let expanded = expand_c0_tactic_source_at(
            click_source,
            &[("all_bits.c", c_source)],
            position.line,
            position.column,
        )
        .expect("bitvector proposition should expand");

        assert!(expanded.contains("result == -1"));
        verify_c0_sources(&expanded, &[("all_bits.c", c_source)])
            .expect("printed negative literal should parse and re-verify");
    }

    #[test]
    fn expanded_branch_certificate_uses_the_branch_entry_state() {
        let c_source = r#"int32 compare_swap2(int32 p[2]) {
    int32 tmp;
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    } else {
        tmp = 0;
    }
    return 0;
}"#;
        let click_source = r#"verifying "compare_swap2.c";
predicate sorted_pair(p: int32[2]) {
    p[0] <= p[1]
}
int32 compare_swap2(int32 p[2]) {
    requires loadable(p[0..2]);
    consumes p[0..2];
    ensures sorted_pair(p) by {
        execute();
        unfold(sorted_pair);
        simp();
    }
}"#;
        let offset = click_source.rfind("simp").expect("simp should be present");
        let position = position_at_offset(click_source, offset);
        let expanded = expand_c0_tactic_source_at(
            click_source,
            &[("compare_swap2.c", c_source)],
            position.line,
            position.column,
        )
        .expect("post-execution simp should expand");

        assert!(expanded.contains("if at(function.entry, *(p + 1))"));
        verify_c0_sources(&expanded, &[("compare_swap2.c", c_source)])
            .expect("branch certificate should replay against the state where it branched");
    }

    #[test]
    fn expanded_contract_let_facts_remain_source_indexable() {
        let c_source = "int32 increment(int32 x) { return x + 1; }";
        let click_source = r#"verifying "increment.c";
int32 increment(int32 x) {
    let max: int32 = 2147483647;
    let expected = x + 1;
    requires x < max;
    ensures result_value: result == expected by auto;
}"#;
        let offset = click_source.find("auto").expect("auto should be present");
        let position = position_at_offset(click_source, offset);
        let expanded = expand_c0_tactic_source_at(
            click_source,
            &[("increment.c", c_source)],
            position.line,
            position.column,
        )
        .expect("contract-let proof should expand");

        assert!(expanded.contains("(let max = 2147483647; 2147483647)"));
        verify_c0_sources(&expanded, &[("increment.c", c_source)])
            .expect("parenthesized contract lets should re-verify");
        c0_tactic_source_position(
            &expanded,
            &[("increment.c", c_source)],
            "increment.result_value",
            0,
        )
        .expect("semicolons inside contract lets must not split source tactics");
    }

    #[test]
    fn expanded_post_execution_apply_retains_its_facts_for_the_closer() {
        let c_source = "int32 inspect(uint8 p[], int32 len) { return 0; }";
        let click_source = r#"verifying "inspect.c";
int32 inspect(uint8 p[], int32 len) {
    requires loadable(p[0..len + 1]);
    requires exact: cstr_len(p, len);
    ensures 0 <= len by {
        execute();
        apply(cstr_len_nonnegative(p, len));
        simp();
    }
}"#;
        let offset = click_source.find("apply").expect("apply should be present");
        let position = position_at_offset(click_source, offset);
        let expanded = expand_c0_tactic_source_at(
            click_source,
            &[("inspect.c", c_source)],
            position.line,
            position.column,
        )
        .expect("post-execution apply should expand");

        assert!(expanded.contains("apply(cstr_len_nonnegative(p, len)) using"));
        verify_c0_sources(&expanded, &[("inspect.c", c_source)])
            .expect("explicit apply conclusions should remain available to the trailing simp");
    }

    #[test]
    fn expansion_retains_callees_used_by_an_earlier_claim() {
        let callee_source = r#"int32 set_cell(int32 p[], int32 value) {
    p[0] = value;
    return value;
}"#;
        let caller_source = r#"int32 set_then_read(int32 p[], int32 value) {
    int32 ignored;
    ignored = set_cell(p, value);
    return p[0];
}"#;
        let click_source = r#"verifying "set_cell.c";
verifying "set_then_read.c";
int32 set_cell(int32 p[], int32 value) {
    owns p[0..1] by auto;
    mutable p[0..1] by { execute(); frame(); }
    ensures p[0] == value by auto;
    ensures result == value by auto;
}
int32 set_then_read(int32 p[], int32 value) {
    owns p[0..1] by {
        step();
        step();
        step();
    }
    ensures result == value by {
        step();
        step();
        step();
        simp();
    }
}"#;
        let sources = [
            ("set_cell.c", callee_source),
            ("set_then_read.c", caller_source),
        ];
        let position =
            c0_tactic_source_position(click_source, &sources, "set_then_read.ensures_1", 0)
                .expect("later claim should have a source tactic");
        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
                .expect("selected later-claim tactic should expand with the callee available");

        verify_c0_sources(&expanded, &sources)
            .expect("expanded later claim should re-verify with its earlier claim");
    }

    #[test]
    fn expands_an_unreachable_omitted_loop_phase() {
        let c_source = r#"int32 branch_count(int32 flag, int32 i) {
    if (flag) {
        while (i < 1) {
            i = i + 1;
        }
    } else {
        i = 1;
    }
    return i;
}"#;
        let click_source = r#"verifying "branch_count.c";
int32 branch_count(int32 flag, int32 i) {
    requires i == 1;
    requires flag != 0;
    for loop(0) {
        invariant i == 1;
    }
    ensures result == 1 by auto;
}"#;
        let sources = [("branch_count.c", c_source)];
        let position =
            c0_tactic_source_position(click_source, &sources, "branch_count.loop(0).preserve", 0)
                .expect("omitted preservation should have a selector");
        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
                .expect("unreachable omitted preservation should expand");

        assert!(expanded.contains("preserve by {\n            assumption();"));
        verify_c0_sources(&expanded, &sources)
            .expect("canonical unreachable phase certificate should re-verify");
    }

    #[test]
    fn expands_a_deferred_tactic_in_one_nested_proof_branch() {
        let c_source = r#"int32 nested(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
        if (y > 0) { y = y + 1; } else { y = 0; }
    } else {
        y = 0;
    }
    return y;
}"#;
        let click_source = r#"verifying "nested.c";
int32 nested(int32 x) {
    requires x < 2147483647;
    ensures result >= 0 by {
        step();
        if x >= 0 {
            step();
            step();
            if y > 0 {
                step();
                step();
                step();
                simp();
            } else {
                step();
                step();
                step();
                simp();
            }
        } else {
            step();
            step();
            step();
            simp();
        }
    }
}"#;
        let needle =
            "step();\n                step();\n                step();\n                simp";
        let offset = click_source
            .find(needle)
            .map(|start| start + needle.rfind("simp").unwrap())
            .expect("inner else simp should be present");
        let position = position_at_offset(click_source, offset);
        let expanded = expand_c0_tactic_source_at(
            click_source,
            &[("nested.c", c_source)],
            position.line,
            position.column,
        )
        .expect("selected nested-branch simp should expand");

        assert_eq!(expanded.matches("simp();").count(), 2);
        verify_c0_sources(&expanded, &[("nested.c", c_source)])
            .expect("sibling proof cases must not steal the deferred capture");
    }

    #[test]
    fn expanded_symbolic_range_propositions_use_parser_syntax() {
        let c_source = "int32 identity(int32 x, int32 n) { return x; }";
        let click_source = r#"verifying "identity.c";
int32 identity(int32 x, int32 n) {
    requires (0..n).any(|k| { k == x });
    ensures same_any: (0..n).any(|k| { k == x }) by auto;
}"#;
        let offset = click_source.find("auto").expect("auto should be present");
        let position = position_at_offset(click_source, offset);
        let expanded = expand_c0_tactic_source_at(
            click_source,
            &[("identity.c", c_source)],
            position.line,
            position.column,
        )
        .expect("symbolic range proposition should expand");

        assert!(expanded.contains("(0..n).any(|k| { k == x })"));
        verify_c0_sources(&expanded, &[("identity.c", c_source)])
            .expect("printed symbolic range proposition should re-verify");
    }

    #[test]
    fn expands_omitted_loop_phase_proofs_at_distinct_coordinates() {
        let c_source = "int32 count(int32 n) { while (n > 0) { n = n - 1; } return n; }";
        let click_source = r#"verifying "count.c";
int32 count(int32 n) {
    for loop(0) {
        invariant n == n;
    }
    ensures result == result;
}
"#;
        let initialize = c0_tactic_source_position(
            click_source,
            &[("count.c", c_source)],
            "count.loop(0).initialize",
            0,
        )
        .expect("omitted initialization should have a selector coordinate");
        let preserve = c0_tactic_source_position(
            click_source,
            &[("count.c", c_source)],
            "count.loop(0).preserve",
            0,
        )
        .expect("omitted preservation should have a selector coordinate");
        assert_ne!(initialize, preserve);

        for position in [initialize, preserve] {
            let expanded = expand_c0_tactic_source_at(
                click_source,
                &[("count.c", c_source)],
                position.line,
                position.column,
            )
            .expect("omitted loop phase should expand to an inserted certificate");
            assert!(expanded.contains(" by {\n"));
            verify_c0_sources(&expanded, &[("count.c", c_source)])
                .expect("inserted loop-phase certificate should re-verify");
        }
    }

    #[test]
    fn expands_single_smart_and_default_function_proofs_by_source_location() {
        let c_source = "int32 identity(int32 x) { return x; }";
        let smart = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x by { execute(); simp(); }
}
"#;
        let smart_position = position_at_offset(smart, smart.find("simp").unwrap());
        let smart_expanded = expand_c0_tactic_source_at(
            smart,
            &[("identity.c", c_source)],
            smart_position.line,
            smart_position.column,
        )
        .expect("single smart proof should expand as a whole proof");
        assert!(smart_expanded.contains("execute();"));
        assert!(!smart_expanded.contains("simp();"));
        verify_c0_sources(&smart_expanded, &[("identity.c", c_source)]).unwrap();

        let implicit = r#"verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
}
"#;
        let implicit_position = position_at_offset(implicit, implicit.find("ensures").unwrap());
        let implicit_expanded = expand_c0_tactic_source_at(
            implicit,
            &[("identity.c", c_source)],
            implicit_position.line,
            implicit_position.column,
        )
        .expect("default proof should expand from its clause coordinate");
        assert!(implicit_expanded.contains("ensures result == x by {"));
        verify_c0_sources(&implicit_expanded, &[("identity.c", c_source)]).unwrap();
    }

    #[test]
    fn whole_function_proof_expansion_skips_unrelated_broken_proofs() {
        let good_c = "int32 good(int32 x) { return x; }";
        let bad_c = "int32 bad(int32 x) { return x; }";
        let click_source = r#"verifying "good.c";
verifying "bad.c";
int32 good(int32 x) {
    ensures result == x;
}
int32 bad(int32 x) {
    ensures result == x + 1 by simp;
}
"#;
        let sources = [("good.c", good_c), ("bad.c", bad_c)];
        verify_c0_sources(click_source, &sources)
            .expect_err("the unrelated bad proof should fail complete verification");
        let selected = position_at_offset(click_source, click_source.find("ensures").unwrap());

        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
                .expect("whole-proof expansion should verify only the selected function");

        assert!(expanded.contains("ensures result == x by {"));
        verify_c0_sources_at(&expanded, &sources, selected.line, selected.column)
            .expect("the expanded selected function should verify independently");
    }

    #[test]
    fn partial_tactic_expansion_skips_unrelated_broken_proofs() {
        let good_c = "int32 good(int32 x) { return x; }";
        let bad_c = "int32 bad(int32 x) { return x; }";
        let click_source = r#"verifying "good.c";
verifying "bad.c";
int32 good(int32 x) {
    ensures result == x by { execute(); simp(); }
}
int32 bad(int32 x) {
    ensures result == x + 1 by simp;
}
"#;
        let sources = [("good.c", good_c), ("bad.c", bad_c)];
        verify_c0_sources(click_source, &sources)
            .expect_err("the unrelated bad proof should fail complete verification");
        let selected_offset = click_source.find("execute();").unwrap();
        let selected = position_at_offset(click_source, selected_offset);

        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
                .expect("partial expansion should verify only the selected function");

        assert_ne!(expanded, click_source);
        assert_eq!(
            &expanded[..selected_offset],
            &click_source[..selected_offset]
        );
        let unselected_suffix = &click_source[selected_offset + "execute();".len()..];
        assert!(expanded.ends_with(unselected_suffix));
        let relocated =
            c0_tactic_source_position(&expanded, &sources, "good.ensures_0", 0).unwrap();
        verify_c0_sources_at(&expanded, &sources, relocated.line, relocated.column)
            .expect("the expanded selected function should verify independently");
        verify_c0_sources(&expanded, &sources)
            .expect_err("whole-file verification should still see the unrelated failure");
    }

    #[test]
    fn tactic_expansion_reports_required_dependency_path() {
        let callee_c = "int32 callee(int32 x) { return x; }";
        let caller_c = "int32 caller(int32 x) { int32 result; result = callee(x); return result; }";
        let click_source = r#"verifying "callee.c";
verifying "caller.c";
int32 callee(int32 x) {
    ensures result == x + 1 by { execute(); simp(); }
}
int32 caller(int32 x) {
    ensures result == x by { execute(); simp(); }
}
"#;
        let sources = [("callee.c", callee_c), ("caller.c", caller_c)];
        let selected = position_at_offset(click_source, click_source.rfind("execute();").unwrap());

        let error =
            expand_c0_tactic_source_at(click_source, &sources, selected.line, selected.column)
                .expect_err("a broken required dependency must block expansion");

        assert!(
            error.message().contains("caller -> callee"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn pure_theorem_expansion_is_certificate_backed_and_idempotent() {
        let source = r#"theorem incremented_zero_is_one(before: int32, after: int32) {
    requires before == 0;
    requires after == before + 1;
    ensures after == 1 by {
        rewrite(after == before + 1);
        rewrite(before == 0);
        simp();
    }
}
"#;
        let expanded_once = expand_pure_theorem_source(source, &[], "incremented_zero_is_one", 0)
            .expect("smart theorem script should expand");
        let expanded_twice =
            expand_pure_theorem_source(&expanded_once, &[], "incremented_zero_is_one", 0)
                .expect("expanded theorem certificate should expand again");

        assert!(!expanded_once.contains("simp"));
        assert_eq!(expanded_once, expanded_twice);
        let verified =
            verify_click_theorems(&expanded_once).expect("expanded theorem should re-verify");
        verified[0]
            .proof_certificate()
            .expect("expanded theorem should retain a surface certificate");
    }
}
