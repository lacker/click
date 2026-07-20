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
    let span = if grouped || claim == CProofClaim::Grouped {
        find_grouped_proof_span(&tokens, &function)?
    } else {
        find_claim_proof_span(&tokens, &function, claim)?
    };
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let mut expanded =
        String::with_capacity(click_source.len() - (span.end - span.start) + replacement.len());
    expanded.push_str(&click_source[..span.start]);
    expanded.push_str(&replacement);
    expanded.push_str(&click_source[span.end..]);
    Ok(expanded)
}

pub fn expand_c0_tactic_source(
    click_source: &str,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: CProofClaim,
    tactic_index: usize,
) -> Result<String, ClickError> {
    let replacement_tactics = super::proof::capture_c0_tactic_expansion(
        click_source,
        c_sources,
        function_name,
        claim,
        tactic_index,
    )?;
    let replacement = super::printing::format_partial_tactic_sequence(&replacement_tactics);
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let proof = match claim {
        CProofClaim::Grouped => find_grouped_proof_span(&tokens, &function)?,
        CProofClaim::Ensure(_) | CProofClaim::Effect(_) => {
            find_claim_proof_span(&tokens, &function, claim)?
        }
    };
    let span = find_tactic_span(&tokens, &proof, tactic_index)?;
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
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index].is_ascii_whitespace() {
            index += 1;
            continue;
        }
        let start = index;
        if bytes[index].is_ascii_alphabetic() || bytes[index] == b'_' {
            index += 1;
            while index < bytes.len()
                && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
            {
                index += 1;
            }
        } else if bytes[index].is_ascii_digit() {
            index += 1;
            while index < bytes.len() && bytes[index].is_ascii_digit() {
                index += 1;
            }
        } else if matches!(bytes[index], b'"' | b'\'') {
            let quote = bytes[index];
            index += 1;
            while index < bytes.len() && bytes[index] != quote {
                if bytes[index] == b'\\' {
                    index += 1;
                }
                index += 1;
            }
            if index == bytes.len() {
                return Err(ClickError::new(
                    "unterminated literal while locating proof source",
                ));
            }
            index += 1;
        } else {
            index += 1;
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
                            "by" if nested == 0 => return proof_span(tokens, cursor),
                            ";" if nested == 0 => {
                                return Err(ClickError::new(format!(
                                    "selected {claim:?} uses a default proof and has no source proof clause to replace"
                                )));
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
    let mut tactic_index = 0;
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
        if tactic_index == wanted {
            return Ok(tokens[start].span.start..tokens[end].span.end);
        }
        tactic_index += 1;
        start = end + 1;
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

        let expanded = expand_c0_tactic_source(
            click_source,
            &[("identity.c", c_source)],
            "identity",
            CProofClaim::Grouped,
            0,
        )
        .expect("the first grouped tactic should expand");

        assert!(!expanded.contains("execute_rest();"));
        assert!(expanded.contains("    execute_step();\n    simp();"));
        verify_c0_sources(&expanded, &[("identity.c", c_source)])
            .expect("the source with one expanded tactic should re-verify");
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

        let expanded =
            expand_c0_tactic_source(click_source, &sources, "caller", CProofClaim::Grouped, 0)
                .expect("opaque call internals should not become surface premises");

        assert_eq!(expanded.matches("execute_rest();").count(), 1);
        verify_c0_sources(&expanded, &sources)
            .expect("the caller with one expanded tactic should re-verify");
    }

    #[test]
    fn selected_tactic_skips_unreached_call_dependencies_and_proof_suffix() {
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

        let expanded =
            expand_c0_tactic_source(click_source, &sources, "caller", CProofClaim::Grouped, 0)
                .expect("the declaration prefix should not verify an unreached callee or suffix");

        assert!(expanded.contains("step();\n    execute_rest();"));
        assert!(verify_c0_sources(&expanded, &sources).is_err());
    }
}
