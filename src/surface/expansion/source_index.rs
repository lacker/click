//! An immutable lexical index shared by every location query in one trace.
use super::*;
use std::collections::{BTreeSet, HashMap};

thread_local! {
    static TOKENIZATION_WORK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(super) fn record_tokenization_work(bytes: usize) {
    TOKENIZATION_WORK.with(|work| work.set(work.get().saturating_add(bytes)));
}

#[derive(Default)]
struct IndexedTactic {
    end: usize,
    body: Option<(usize, usize)>,
    arms: Vec<(usize, usize)>,
    arm_ranges: Vec<(usize, usize, usize)>,
}

/// Source positions and proof-block structure for an immutable Click container.
/// Construction walks the source once and skips indexed delimiter groups when
/// inspecting a block's direct children. Queries never tokenize or scan source.
pub struct ProofSourceIndex {
    tokens: Vec<SourceToken>,
    pairs: Vec<Option<usize>>,
    characters: Vec<usize>,
    lines: Vec<usize>,
    positions: Vec<SourcePosition>,
    by_offset: HashMap<usize, usize>,
    blocks: HashMap<usize, Vec<usize>>,
    tactics: HashMap<usize, IndexedTactic>,
    starts: Vec<Vec<usize>>,
}

impl ProofSourceIndex {
    /// Bytes tokenized on this thread, independently of verification budgets.
    /// Scaling regressions use differences to detect repeated whole-file scans.
    pub fn tokenization_work() -> usize {
        TOKENIZATION_WORK.with(std::cell::Cell::get)
    }

    pub fn new(source: &str) -> Result<Self, ClickError> {
        crate::instrumentation::record_deterministic_work(source.len());
        let tokens = scan_source_tokens(source)?;
        let mut pairs = vec![None; tokens.len()];
        let mut stack = Vec::new();
        for (index, token) in tokens.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            match token.text.as_str() {
                "(" | "[" | "{" => stack.push(index),
                ")" | "]" | "}" => {
                    let open = stack
                        .pop()
                        .ok_or_else(|| ClickError::new("unbalanced source delimiters"))?;
                    if !matches!(
                        (tokens[open].text.as_str(), token.text.as_str()),
                        ("(", ")") | ("[", "]") | ("{", "}")
                    ) {
                        return Err(ClickError::new("unbalanced source delimiters"));
                    }
                    pairs[open] = Some(index);
                }
                _ => {}
            }
        }
        if !stack.is_empty() {
            return Err(ClickError::new("unbalanced source delimiters"));
        }
        let mut characters = Vec::new();
        let mut lines = vec![0];
        for (offset, character) in source.char_indices() {
            characters.push(offset);
            if character == '\n' {
                lines.push(characters.len());
            }
        }
        characters.push(source.len());
        let mut result = Self {
            positions: Vec::with_capacity(tokens.len()),
            by_offset: HashMap::new(),
            starts: vec![Vec::new(); lines.len()],
            tokens,
            pairs,
            characters,
            lines,
            blocks: HashMap::new(),
            tactics: HashMap::new(),
        };
        for index in 0..result.tokens.len() {
            let offset = result.tokens[index].span.start;
            result.positions.push(result.position_at(offset));
            // Synthetic braces share the next written token's offset. A
            // diagnostic position names that written token, not the brace.
            if !result.tokens[index].span.is_empty() {
                result.by_offset.entry(offset).or_insert(index);
            }
        }
        let mut arm_blocks = BTreeSet::new();
        let mut open_since_boundary = false;
        for open in 0..result.tokens.len() {
            crate::instrumentation::record_deterministic_work(1);
            let text = result.tokens[open].text.as_str();
            if text != "{" {
                if text == "open" {
                    open_since_boundary = true;
                }
                if matches!(text, ";" | "}") {
                    open_since_boundary = false;
                }
                continue;
            }
            let previous = open.checked_sub(1).map(|i| result.tokens[i].text.as_str());
            let direct = matches!(previous, Some("by" | "then" | "else" | "and" | "both"))
                || (open >= 2 && result.tokens[open - 2].text == "=" && previous == Some(">"));
            let is_open_body = previous == Some(")") && open_since_boundary;
            open_since_boundary = false;
            if !direct && !is_open_body && !arm_blocks.contains(&open) {
                continue;
            }
            let close = result.pairs[open].expect("balanced opening brace");
            let Ok(ranges) = result.direct_ranges(open, close) else {
                continue;
            };
            let mut children = Vec::new();
            for range in ranges {
                let start = range.start;
                let tactic = result.describe_tactic(start, range.end - 1);
                arm_blocks.extend(tactic.arms.iter().map(|&(open, _)| open));
                let line = result.positions[start].line - 1;
                result.starts[line].push(result.tokens[start].span.start);
                result.tactics.insert(start, tactic);
                children.push(start);
            }
            result.blocks.insert(open, children);
        }
        for starts in &mut result.starts {
            starts.sort_unstable();
            starts.dedup();
        }
        Ok(result)
    }

    fn position_at(&self, offset: usize) -> SourcePosition {
        let character = self.characters.partition_point(|&start| start < offset);
        let line = self.lines.partition_point(|&start| start <= character) - 1;
        SourcePosition::new(line + 1, character - self.lines[line] + 1)
    }

    fn offset(&self, position: &SourcePosition) -> Result<usize, ClickError> {
        let line = position
            .line
            .checked_sub(1)
            .and_then(|i| self.lines.get(i))
            .copied()
            .ok_or_else(|| ClickError::new("source line is missing"))?;
        let character = position
            .column
            .checked_sub(1)
            .and_then(|c| line.checked_add(c))
            .ok_or_else(|| ClickError::new("source column is missing"))?;
        if self
            .lines
            .get(position.line)
            .is_some_and(|&next| character >= next)
        {
            return Err(ClickError::new("source column is missing"));
        }
        self.characters
            .get(character)
            .copied()
            .ok_or_else(|| ClickError::new("source column is missing"))
    }

    fn token(&self, position: &SourcePosition) -> Result<usize, ClickError> {
        self.by_offset
            .get(&self.offset(position)?)
            .copied()
            .ok_or_else(|| ClickError::new("could not locate source tactic"))
    }

    fn end(&self, start: usize, limit: usize) -> Result<usize, ClickError> {
        let mut cursor = start;
        let mut have_body_started = self.tokens[start].text != "have";
        while cursor < limit {
            crate::instrumentation::record_deterministic_work(1);
            match self.tokens[cursor].text.as_str() {
                "by" => have_body_started = true,
                "(" | "[" => {
                    cursor = self.pairs[cursor]
                        .ok_or_else(|| ClickError::new("unbalanced source tactic"))?
                }
                "{" => {
                    cursor = self.pairs[cursor]
                        .ok_or_else(|| ClickError::new("unbalanced source tactic"))?;
                    let next = self.tokens.get(cursor + 1).map(|t| t.text.as_str());
                    let kind = self.tokens[start].text.as_str();
                    if have_body_started
                        && !(matches!(next, Some("else" | "by" | "="))
                            || (kind == "both" && next == Some("and"))
                            || (kind == "match" && next == Some("{"))
                            || (matches!(kind, "branch" | "if") && next == Some("then")))
                    {
                        return Ok(cursor + usize::from(next == Some(";")));
                    }
                }
                ";" => return Ok(cursor),
                _ => {}
            }
            cursor += 1;
        }
        Err(ClickError::new(
            "unterminated tactic in selected source proof",
        ))
    }

    fn direct_ranges(&self, open: usize, close: usize) -> Result<Vec<Range<usize>>, ClickError> {
        let mut ranges = Vec::new();
        let mut start = open + 1;
        while start < close {
            let end = self.end(start, close)?;
            ranges.push(start..end + 1);
            start = end + 1;
        }
        Ok(ranges)
    }

    fn describe_tactic(&self, start: usize, end: usize) -> IndexedTactic {
        let mut result = IndexedTactic {
            end,
            ..Default::default()
        };
        let kind = self.tokens[start].text.as_str();
        let mut cursor = start + 1;
        let mut by = false;
        let mut returned = None;
        let mut threw = None;
        while cursor <= end {
            crate::instrumentation::record_deterministic_work(1);
            let text = self.tokens[cursor].text.as_str();
            if text == "by" {
                by = true;
            }
            if matches!(text, "(" | "[") {
                cursor = self.pairs[cursor].expect("balanced group") + 1;
                continue;
            }
            if text == "{" {
                let close = self.pairs[cursor].expect("balanced block");
                let block = (cursor, close);
                if (kind == "have" && by) || kind == "open" {
                    result.body = Some(block);
                    break;
                }
                if matches!(kind, "cases" | "outcomes") && cursor == start + 1 {
                    // Inspect arm headers, skipping each arm's contents and
                    // any quantifier in its assumption.
                    let mut arm = cursor + 1;
                    while arm < close {
                        crate::instrumentation::record_deterministic_work(1);
                        if self.tokens[arm].text == "{" {
                            let arm_close = self.pairs[arm].expect("balanced arm");
                            if arm >= 2
                                && self.tokens[arm - 2].text == "="
                                && self.tokens[arm - 1].text == ">"
                            {
                                if kind == "cases" {
                                    result.arms.push((arm, arm_close));
                                } else if arm >= 3 {
                                    match self.tokens[arm - 3].text.as_str() {
                                        "returned" => returned = Some((arm, arm_close)),
                                        "threw" => threw = Some((arm, arm_close)),
                                        _ => {}
                                    }
                                }
                            }
                            arm = arm_close + 1;
                        } else {
                            arm += 1;
                        }
                    }
                } else if (kind == "if"
                    && (self.tokens.get(close + 1).is_some_and(|t| t.text == "else")
                        || self.tokens[cursor - 1].text == "else"))
                    || (kind == "branch"
                        && matches!(self.tokens[cursor - 1].text.as_str(), "then" | "else"))
                    || kind == "both"
                {
                    result.arms.push(block);
                }
                cursor = close + 1;
            } else {
                cursor += 1;
            }
        }
        if kind == "outcomes"
            && let (Some(returned), Some(threw)) = (returned, threw)
        {
            result.arms = vec![returned, threw];
        }
        result.arm_ranges = result
            .arms
            .iter()
            .enumerate()
            .map(|(index, &(open, close))| {
                (
                    self.tokens[open].span.start,
                    self.tokens[close].span.end,
                    index,
                )
            })
            .collect();
        result.arm_ranges.sort_unstable();
        result
    }

    /// Claim roots use the same token stream as nested paths and containment.
    pub fn project_tactic_positions(
        &self,
        project: &ClickProject,
        inputs: &ProgramInputs<'_>,
        claim: &str,
    ) -> Result<Vec<SourcePosition>, ClickError> {
        let sources = CSourceContext::of(inputs)?.with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        c0_tactic_source_positions_with_tokens(
            &file,
            project.entry_source().expect("resolved entry source"),
            claim,
            &self.tokens,
        )
    }

    pub fn nested_position(
        &self,
        outer: &SourcePosition,
        nested: &[usize],
    ) -> Result<SourcePosition, ClickError> {
        let mut current = self.token(outer)?;
        let mut indices = nested.iter().copied();
        while let Some(index) = indices.next() {
            crate::instrumentation::record_deterministic_work(1);
            let tactic = self
                .tactics
                .get(&current)
                .ok_or_else(|| ClickError::new("source tactic has no nested body"))?;
            let (open, child) =
                if matches!(self.tokens[current].text.as_str(), "if" | "cases" | "both") {
                    let &(open, _) = tactic
                        .arms
                        .get(index)
                        .ok_or_else(|| ClickError::new("source arm is missing"))?;
                    (
                        open,
                        indices
                            .next()
                            .ok_or_else(|| ClickError::new("source arm tactic is missing"))?,
                    )
                } else {
                    (
                        tactic
                            .body
                            .ok_or_else(|| ClickError::new("source tactic body is missing"))?
                            .0,
                        index,
                    )
                };
            current = *self
                .blocks
                .get(&open)
                .and_then(|children| children.get(child))
                .ok_or_else(|| ClickError::new("nested source tactic is missing"))?;
        }
        Ok(self.positions[current].clone())
    }

    /// The written tactic and its indentation, without another source scan.
    pub fn tactic_text<'a>(
        &self,
        source: &'a str,
        position: &SourcePosition,
    ) -> Result<(&'a str, &'a str), ClickError> {
        let start = self.token(position)?;
        let end = match self.tactics.get(&start) {
            Some(tactic) => tactic.end,
            None => self.end(start, self.tokens.len())?,
        };
        let offset = self.offset(position)?;
        let line_start = self.characters[self.lines[position.line - 1]];
        Ok((
            &source[self.tokens[start].span.start..self.tokens[end].span.end],
            &source[line_start..offset],
        ))
    }

    pub fn line_has_multiple_starts(&self, position: &SourcePosition) -> Result<bool, ClickError> {
        crate::instrumentation::record_deterministic_work(1);
        let selected = self.offset(position)?;
        let starts = &self.starts[position.line - 1];
        let present = starts.binary_search(&selected).is_ok();
        if starts.len() + usize::from(!present) <= 1 {
            return Ok(false);
        }
        if starts.first().copied() != Some(selected) {
            return Ok(true);
        }
        let Some(&start) = self.by_offset.get(&selected) else {
            return Ok(true);
        };
        let end = self.tactics.get(&start).map(|t| t.end);
        let Some(end) = end else {
            return Ok(true);
        };
        // The greatest start suffices: nested starts before this tactic's
        // end do not make the outer tactic's line ambiguous.
        Ok(starts
            .last()
            .is_some_and(|&offset| offset >= self.tokens[end].span.end))
    }

    pub fn arm_containing(
        &self,
        tactic: &SourcePosition,
        target: &SourcePosition,
    ) -> Result<Option<usize>, ClickError> {
        let start = self.token(tactic)?;
        let target = self.offset(target)?;
        let Some(tactic) = self.tactics.get(&start) else {
            return Ok(None);
        };
        let after = tactic.arm_ranges.partition_point(|&(open, _, _)| {
            crate::instrumentation::record_deterministic_work(1);
            open < target
        });
        if let Some(&(open, close, index)) =
            after.checked_sub(1).and_then(|i| tactic.arm_ranges.get(i))
            && open < target
            && target < close
        {
            return Ok(Some(index));
        }
        Ok(None)
    }

    pub fn have_body_contains(
        &self,
        tactic: &SourcePosition,
        target: &SourcePosition,
    ) -> Result<bool, ClickError> {
        crate::instrumentation::record_deterministic_work(1);
        let start = self.token(tactic)?;
        if self.tokens[start].text != "have" {
            return Ok(false);
        }
        let target = self.offset(target)?;
        let Some((open, close)) = self.tactics.get(&start).and_then(|t| t.body) else {
            return Ok(false);
        };
        Ok(self.tokens[open].span.start < target && target < self.tokens[close].span.end)
    }
}
