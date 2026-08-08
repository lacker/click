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
                    nested_source_index += proof_source_tactic_count(proof);
                }
                for item in clause.items() {
                    if !item.is_effect_kind() {
                        continue;
                    }
                    collect_smart_nested_proof_sites(
                        claim_label,
                        item.proof(),
                        nested_source_index,
                        sites,
                    );
                    nested_source_index += proof_source_tactic_count(item.proof());
                }
            }
            _ => {}
        }
        source_index += source_tactic_count(std::slice::from_ref(tactic));
    }
}

fn collect_smart_nested_proof_sites(
    claim_label: &str,
    proof: &Proof,
    source_index: usize,
    sites: &mut Vec<SmartTacticSourceSite>,
) {
    match proof {
        Proof::Default => {}
        Proof::Tactic(tactic) => sites.push(SmartTacticSourceSite {
            claim_label: claim_label.to_string(),
            source_index,
            tactic_name: match tactic {
                SmartTactic::Auto => "auto",
                SmartTactic::Frame => "frame",
                SmartTactic::Simp => "simp",
            }
            .to_string(),
        }),
        Proof::Script(tactics) => {
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
        TacticSourceEdit::Partial(_) | TacticSourceEdit::PartialProofClause(_) => {
            super::proof::capture_c0_tactic_expansion(
                click_source,
                c_sources,
                selected.site.clone(),
                selected.source_index,
            )?
        }
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
        TacticSourceEdit::PartialProofClause(span) => {
            let certificate =
                TacticCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: {error:?}"
                    ))
                })?;
            (
                span,
                super::printing::format_tactic_certificate(&certificate),
            )
        }
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
            let ProofSourceEdit::Explicit(source_proof_span) = edit else {
                return Err(ClickError::new(
                    "an explicit proof script has no source `by` clause",
                ));
            };
            let spans = collect_source_tactic_spans(tokens, source_proof_span, tactics)?;
            let Some((source_index, span)) = spans
                .into_iter()
                .enumerate()
                .find(|(_, span)| span.start == wanted)
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

fn source_tactic_is_nested_proof_clause(tactics: &[ProofTactic], wanted: usize) -> bool {
    fn in_proof(proof: &Proof, wanted: usize, source_index: usize) -> Option<bool> {
        match proof {
            Proof::Default => None,
            Proof::Tactic(_) => (wanted == source_index).then_some(true),
            Proof::Script(tactics) => find(tactics, wanted, source_index),
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
                        nested_source_index += proof_source_tactic_count(proof);
                    } else if let Some(proof) = clause.preserve_proof() {
                        nested_source_index += proof_source_tactic_count(proof);
                    }
                    if found.is_none() {
                        for item in clause.items().iter().filter(|item| item.is_effect_kind()) {
                            found = in_proof(item.proof(), wanted, nested_source_index);
                            nested_source_index += proof_source_tactic_count(item.proof());
                            if found.is_some() {
                                break;
                            }
                        }
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
                for (item, edit) in clause.items().iter().zip(&edits) {
                    if !item.is_effect_kind() {
                        continue;
                    }
                    collect_nested_proof_spans(tokens, edit, item.proof(), spans)?;
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
    proof: &Proof,
    spans: &mut Vec<Range<usize>>,
) -> Result<(), ClickError> {
    match proof {
        Proof::Default => Ok(()),
        Proof::Tactic(_) => {
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
        Proof::Script(tactics) => {
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
                            let terminator = if continuation == Some(";") {
                                cursor + 1
                            } else {
                                cursor
                            };
                            break terminator;
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

fn find_branch_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
) -> Result<(usize, usize, usize, usize), ClickError> {
    let outer_open = (tactic.start + 1..tactic.end)
        .find(|index| tokens[*index].text == "{")
        .ok_or_else(|| ClickError::new("source `branch` tactic has no body"))?;
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
            "could not locate `branch` {name} arm"
        )))
    };
    let (then_open, then_close) = find_named_block("then")?;
    let (else_open, else_close) = find_named_block("else")?;
    Ok((then_open, then_close, else_open, else_close))
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
