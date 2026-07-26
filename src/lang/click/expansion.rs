use std::ops::Range;

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
    let verified = verify_c0_sources(click_source, c_sources)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = theorem.expanded_proof_source()?;
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let grouped = theorem.function_block.grouped_proof().is_some();
    let edit = if grouped || claim == CProofClaim::Grouped {
        ProofSourceEdit::Explicit(find_grouped_proof_span(&tokens, &function)?)
    } else {
        find_claim_proof_edit(&tokens, &function, claim)?
    };
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator(_) => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
    };
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    Ok(expanded)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourcePosition {
    pub line: usize,
    pub column: usize,
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
    expand_c0_tactic_source_index(
        click_source,
        c_sources,
        &selected.function_name,
        selected.claim,
        selected.source_index,
        selected.span,
    )
}

fn expand_c0_tactic_source_index(
    click_source: &str,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: CProofClaim,
    source_index: usize,
    span: Range<usize>,
) -> Result<String, ClickError> {
    let replacement_tactics = super::proof::capture_c0_tactic_expansion(
        click_source,
        c_sources,
        function_name,
        claim,
        source_index,
    )?;
    let replacement = super::printing::format_partial_tactic_sequence(&replacement_tactics);
    let replacement = indent_replacement(click_source, span.start, &replacement);
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
            matches_function(&theorem)
                && matches!(theorem.claim, VerifiedClaim::Ensure { index: found, .. } if found == index)
        }),
        CProofClaim::Effect(index) => verified.iter().find(|theorem| {
            matches_function(&theorem)
                && matches!(theorem.claim, VerifiedClaim::Effect { index: found, .. } if found == index)
        }),
        CProofClaim::Grouped => verified
            .iter()
            .find(|theorem| {
                matches_function(&theorem)
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
        ProofSourceEdit::DefaultTerminator(_) => Err(ClickError::new(format!(
            "selected {claim:?} uses a default proof and has no explicit source tactic"
        ))),
    }
}

#[derive(Clone, Debug)]
enum ProofSourceEdit {
    Explicit(Range<usize>),
    DefaultTerminator(Range<usize>),
}

impl ProofSourceEdit {
    fn span(&self) -> &Range<usize> {
        match self {
            Self::Explicit(span) | Self::DefaultTerminator(span) => span,
        }
    }
}

fn find_claim_proof_edit(
    tokens: &[SourceToken],
    function: &FunctionSource,
    claim: CProofClaim,
) -> Result<ProofSourceEdit, ClickError> {
    let (keyword, wanted) = match claim {
        CProofClaim::Ensure(index) => ("ensures", index),
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
                                return Ok(ProofSourceEdit::DefaultTerminator(
                                    tokens[cursor].span.clone(),
                                ));
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

#[derive(Clone, Debug)]
struct LocatedSourceTactic {
    function_name: String,
    claim: CProofClaim,
    source_index: usize,
    span: Range<usize>,
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
    for function_block in file.function_blocks() {
        let function_name = function_block.signature().name();
        let function = find_function(&tokens, function_name)?;
        if let Some(proof) = function_block.grouped_proof() {
            let proof_span = find_grouped_proof_span(&tokens, &function)?;
            if let Some(found) = locate_tactic_in_proof(
                &tokens,
                &proof_span,
                proof,
                wanted,
                function_name,
                CProofClaim::Grouped,
            )? {
                return Ok(found);
            }
            continue;
        }
        for (index, ensure) in function_block.ensures().iter().enumerate() {
            let claim = CProofClaim::Ensure(index);
            let Ok(proof_span) = find_claim_proof_span(&tokens, &function, claim) else {
                continue;
            };
            if let Some(found) = locate_tactic_in_proof(
                &tokens,
                &proof_span,
                ensure.proof(),
                wanted,
                function_name,
                claim,
            )? {
                return Ok(found);
            }
        }
        for (index, effect) in function_block.effects().iter().enumerate() {
            let claim = CProofClaim::Effect(index);
            let Ok(proof_span) = find_claim_proof_span(&tokens, &function, claim) else {
                continue;
            };
            if let Some(found) = locate_tactic_in_proof(
                &tokens,
                &proof_span,
                effect.proof(),
                wanted,
                function_name,
                claim,
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
    proof_span: &Range<usize>,
    proof: &Proof,
    wanted: usize,
    function_name: &str,
    claim: CProofClaim,
) -> Result<Option<LocatedSourceTactic>, ClickError> {
    let Some(tactics) = proof.tactics() else {
        return Ok(None);
    };
    let spans = collect_source_tactic_spans(tokens, proof_span, tactics)?;
    Ok(spans
        .into_iter()
        .enumerate()
        .find(|(_, span)| span.start == wanted)
        .map(|(source_index, span)| LocatedSourceTactic {
            function_name: function_name.to_string(),
            claim,
            source_index,
            span,
        }))
}

pub fn c0_tactic_source_position(
    click_source: &str,
    c_sources: &[(&str, &str)],
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    for function_block in file.function_blocks() {
        let function_name = function_block.signature().name();
        let function = find_function(&tokens, function_name)?;
        if let Some(rest) = claim_label
            .strip_prefix(function_name)
            .and_then(|rest| rest.strip_prefix(".loop("))
        {
            if let Some((loop_index, phase)) = rest.split_once(").")
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
                let (fallback, proof_span) =
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
    let (keyword, wanted) = match claim {
        CProofClaim::Ensure(index) => ("ensures", index),
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
) -> Result<(usize, Option<Range<usize>>), ClickError> {
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
                                    tokens[index].span.start,
                                    Some(proof_span(tokens, by)?),
                                ));
                            }
                            _ => {}
                        }
                    }
                    return Ok((tokens[index].span.start, None));
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

fn position_at_offset(source: &str, offset: usize) -> SourcePosition {
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
            ProofTactic::Advance(advance) => {
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
                    .ok_or_else(|| ClickError::new("unbalanced `advance` tactic source block"))?
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
    Err(ClickError::new("could not locate `advance` proof body"))
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
    execute_rest();
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

        assert!(!expanded.contains("execute_rest();"));
        assert!(expanded.contains("    step();\n    simp();"));
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
    execute_rest();
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

        assert!(!expanded.contains("execute_rest();"));
        assert!(expanded.contains("step using {"));
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
        execute_rest();
        simp();
    } else {
        execute_rest();
        simp();
    }
}
"#;
        let then_offset = click_source
            .find("        execute_rest();")
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

        assert_eq!(expanded.matches("execute_rest();").count(), 1);
        assert!(expanded.contains("    if x == x {\n        step using {"));
        verify_c0_sources(&expanded, &[("identity.c", c_source)])
            .expect("the source with one nested expansion should re-verify");
    }

    #[test]
    fn locates_a_block_tactic_as_one_source_statement() {
        let source = "by { have x == x by { simp(); } simp(); }";
        let tokens = scan_source_tokens(source).expect("source should scan");
        let proof = proof_span(&tokens, 0).expect("proof should have a span");

        let first = find_tactic_span(&tokens, &proof, 0).expect("first tactic should exist");
        let second = find_tactic_span(&tokens, &proof, 1).expect("second tactic should exist");

        assert_eq!(&source[first], "have x == x by { simp(); }");
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
    execute_rest();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute_rest();
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

        assert_eq!(expanded.matches("execute_rest();").count(), 1);
        verify_c0_sources(&expanded, &sources)
            .expect("the caller with one expanded tactic should re-verify");
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
    execute_rest();
    simp();
}

int32 caller() {
    ensures result == 0;
} by {
    execute_step();
    execute_rest();
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
        assert!(error.message().contains("left `zero.ensures_0` unproved"));
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
predicate terminated_at(int32 data[], int32 length) {
    data[length] == 0
}

resource owned_box(owner: struct box*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns (owner->data)[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact terminated_at(owner->data, owner->len);
    fact separate(
        memory(owner[0..3]),
        memory((owner->data)[0..owner->cap])
    );
}

verifying "inspect.c";

int32 inspect(struct box* owner) {
    consumes owned_box(owner);
    ensures result == 0;
} by {
    unfold(owned_box(owner));
    unfold(terminated_at);
    execute_step();
    execute_rest();
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

        assert!(
            expanded.contains(
                "fact terminated_at(load_int32_pointer((owner + 2)), load_int32(owner));"
            )
        );
        assert!(expanded.contains(
            "fact separate(memory(owner[0..3]), memory(load_int32_pointer((owner + 2))[0..load_int32((owner + 1))]));"
        ));
        assert!(expanded.contains("fact load_int32_pointer((owner + 2))[load_int32(owner)] == 0;"));
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
    }
}
