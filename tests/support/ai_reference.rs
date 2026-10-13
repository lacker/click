//! Derived files of the AI reference, built into the rendered site.
//!
//! `docs/SUMMARY.md` is the single source of the reference's order and its two
//! parts. From it this module generates, for the rendered book's output
//! directory (next to `index.html`):
//!
//! - `llms.txt`, an index in the llms.txt convention: one line per page, whose
//!   description is the first sentence of the page's opening paragraph;
//! - `click-reference.md`, every page of the "Using Click" part concatenated
//!   in summary order, for readers that want the whole reference in one file;
//! - each listed page's Markdown source at its own path, so the `.md` links in
//!   both files resolve on the site, as the llms.txt convention expects.
//!
//! Nothing generated is committed. `tests/documentation.rs` runs the
//! generator in memory so a bad page opening fails the gate, and writes the
//! files when [`OUTPUT_VARIABLE`] names a directory, which
//! `scripts/build-ai-reference.sh` and `scripts/check.sh --docs-only` do. A page whose
//! opening is not a prose paragraph, or whose first sentence ends in a colon,
//! is an error: fix the page's opening sentence rather than special-casing it
//! here.

use std::path::{Component, Path, PathBuf};

/// When set, the documentation test writes the generated files into this
/// directory.
pub const OUTPUT_VARIABLE: &str = "CLICK_AI_REFERENCE_OUT";
/// The summary part that the single-file bundle contains.
pub const USING_PART: &str = "Using Click";

const LLMS_TXT: &str = "llms.txt";
const BUNDLE: &str = "click-reference.md";

pub struct Page {
    pub part: String,
    pub title: String,
    /// Path relative to `docs/`.
    pub path: String,
}

/// Lists the summary's pages in order with the part each belongs to. Prefix
/// chapters before the first part heading are an error: every page belongs to
/// one of the two parts.
pub fn summary_pages(summary: &str) -> Result<Vec<Page>, String> {
    let mut part = None::<String>;
    let mut pages = Vec::new();
    for (line, text) in summary.lines().enumerate() {
        let trimmed = text.trim_start();
        if let Some(title) = text.strip_prefix("# ") {
            if title != "Summary" {
                part = Some(title.trim().to_string());
            }
            continue;
        }
        let Some(item) = trimmed
            .strip_prefix("- ")
            .or_else(|| trimmed.starts_with('[').then_some(trimmed))
        else {
            continue;
        };
        let (Some(open), Some(middle)) = (item.find('['), item.rfind("](")) else {
            continue;
        };
        let title = item[open + 1..middle].to_string();
        let path = item[middle + 2..]
            .trim_end()
            .trim_end_matches(')')
            .to_string();
        let Some(part) = part.clone() else {
            return Err(format!(
                "docs/SUMMARY.md:{}: page {path} precedes the first part heading",
                line + 1
            ));
        };
        pages.push(Page { part, title, path });
    }
    if !pages.iter().any(|page| page.part == USING_PART) {
        return Err(format!("docs/SUMMARY.md has no `# {USING_PART}` part"));
    }
    Ok(pages)
}

/// Returns every generated file as (path relative to the site root, contents).
pub fn generate(root: &Path) -> Result<Vec<(String, String)>, String> {
    let docs = root.join("docs");
    let read = |path: &str| {
        std::fs::read_to_string(docs.join(path)).map_err(|error| format!("docs/{path}: {error}"))
    };
    let pages = summary_pages(&read("SUMMARY.md")?)?;
    let mut sources = Vec::new();
    for page in &pages {
        sources.push(read(&page.path)?);
    }

    let index = pages
        .iter()
        .position(|page| page.path == "index.md")
        .ok_or("docs/SUMMARY.md does not list index.md")?;
    let summary = opening_paragraph(&sources[index])
        .map(|paragraph| plain_text(&paragraph))
        .map_err(|error| format!("docs/index.md: {error}"))?;

    let mut llms = String::new();
    llms.push_str("# Click\n\n");
    llms.push_str(&format!("> {summary}\n\n"));
    llms.push_str(&format!(
        "Generated from `docs/SUMMARY.md`. Paths are relative to this file and \
         name each page's Markdown source. The \"{USING_PART}\" pages, in this order, \
         are also concatenated into one file: [{BUNDLE}]({BUNDLE}).\n"
    ));
    let mut current_part = None;
    let mut failures = Vec::new();
    for (page, source) in pages.iter().zip(&sources) {
        if current_part != Some(&page.part) {
            llms.push_str(&format!("\n## {}\n\n", page.part));
            current_part = Some(&page.part);
        }
        match opening_paragraph(source).and_then(|paragraph| first_sentence(&paragraph)) {
            Ok(description) => llms.push_str(&format!(
                "- [{}]({}): {description}\n",
                page.title, page.path
            )),
            Err(error) => failures.push(format!("docs/{}: {error}", page.path)),
        }
    }
    if !failures.is_empty() {
        return Err(format!(
            "pages need a one-sentence opening paragraph for {LLMS_TXT}:\n{}",
            failures.join("\n")
        ));
    }

    let mut bundle = String::new();
    bundle.push_str("<!-- Generated from docs/SUMMARY.md; do not edit. -->\n\n");
    bundle.push_str("# Click reference: using Click\n\n");
    bundle.push_str(&format!(
        "This file is every page of the \"{USING_PART}\" part of the Click AI \
         reference, in reading order. Each page starts with a \
         `<!-- source: PATH -->` marker naming its file under `docs/`. Links are \
         rewritten to those `docs/`-relative paths, so a link to \
         `concepts/trust.md#section` refers to the section of the page marked \
         `<!-- source: concepts/trust.md -->`. The pages about developing Click \
         are not included; [llms.txt]({LLMS_TXT}) lists them.\n"
    ));
    for (page, source) in pages.iter().zip(&sources) {
        if page.part != USING_PART {
            continue;
        }
        bundle.push_str(&format!("\n<!-- source: {} -->\n\n", page.path));
        let rewritten = rewrite_links(&docs, &page.path, source)
            .map_err(|error| format!("docs/{}: {error}", page.path))?;
        bundle.push_str(rewritten.trim_end());
        bundle.push('\n');
    }

    let mut files = vec![(LLMS_TXT.to_string(), llms), (BUNDLE.to_string(), bundle)];
    for (page, source) in pages.iter().zip(sources) {
        files.push((page.path.clone(), source));
    }
    Ok(files)
}

/// The first prose paragraph after the page's H1, with its lines joined.
fn opening_paragraph(source: &str) -> Result<String, String> {
    let mut lines = source.lines().skip_while(|line| !line.starts_with("# "));
    if lines.next().is_none() {
        return Err("no H1".to_string());
    }
    let mut paragraph = Vec::new();
    let mut in_comment = false;
    for line in lines {
        let text = line.trim();
        if in_comment {
            in_comment = !text.contains("-->");
            continue;
        }
        if paragraph.is_empty() {
            if text.is_empty() {
                continue;
            }
            if text.starts_with("<!--") {
                in_comment = !text.contains("-->");
                continue;
            }
            let block = text.starts_with('#')
                || text.starts_with("```")
                || text.starts_with("- ")
                || text.starts_with("* ")
                || text.starts_with('|')
                || text.starts_with('>')
                || text.starts_with("1. ");
            if block {
                return Err(format!(
                    "the H1 is followed by `{text}`, not by a prose paragraph"
                ));
            }
        } else if text.is_empty() {
            break;
        }
        paragraph.push(text);
    }
    if paragraph.is_empty() {
        return Err("no paragraph follows the H1".to_string());
    }
    Ok(paragraph.join(" "))
}

/// The paragraph's first sentence as plain text.
fn first_sentence(paragraph: &str) -> Result<String, String> {
    let text = plain_text(paragraph);
    let chars = text.char_indices().collect::<Vec<_>>();
    let mut in_code = false;
    let mut end = text.len();
    for (position, &(offset, ch)) in chars.iter().enumerate() {
        if ch == '`' {
            in_code = !in_code;
            continue;
        }
        if in_code || !matches!(ch, '.' | '!' | '?') {
            continue;
        }
        let next = chars.get(position + 1).map(|&(_, next)| next);
        if !next.is_none_or(char::is_whitespace) {
            continue;
        }
        let through = &text[..offset + 1];
        if ["e.g.", "i.e.", "etc.", "vs."]
            .iter()
            .any(|abbreviation| through.ends_with(abbreviation))
        {
            continue;
        }
        end = offset + 1;
        break;
    }
    let sentence = text[..end].trim().to_string();
    if sentence.ends_with(':') {
        return Err(format!(
            "the opening sentence introduces a list or example instead of saying what the page is: {sentence}"
        ));
    }
    Ok(sentence)
}

/// Replaces Markdown links by their text and drops bold markers.
fn plain_text(markdown: &str) -> String {
    let mut result = String::new();
    let mut rest = markdown;
    while let Some(open) = rest.find('[') {
        result.push_str(&rest[..open]);
        let after = &rest[open..];
        let mut depth = 0usize;
        let mut close = None;
        for (offset, ch) in after.char_indices() {
            match ch {
                '[' => depth += 1,
                ']' => {
                    depth -= 1;
                    if depth == 0 {
                        close = Some(offset);
                        break;
                    }
                }
                _ => {}
            }
        }
        let link_end = close.and_then(|close| {
            after[close + 1..]
                .starts_with('(')
                .then(|| after[close..].find(')'))
                .flatten()
                .map(|end| (close, close + end))
        });
        match link_end {
            Some((close, end)) => {
                result.push_str(&plain_text(&after[1..close]));
                rest = &after[end + 1..];
            }
            None => {
                result.push('[');
                rest = &after[1..];
            }
        }
    }
    result.push_str(rest);
    result.replace("**", "")
}

/// Rewrites the page's relative links, outside code fences, to paths relative
/// to `docs/`. An in-page anchor `#x` becomes `page.md#x`.
fn rewrite_links(docs: &Path, page: &str, source: &str) -> Result<String, String> {
    let directory = Path::new(page).parent().unwrap_or(Path::new(""));
    let mut output = String::new();
    let mut in_fence = false;
    for line in source.split_inclusive('\n') {
        if line.trim_start().starts_with("```") {
            in_fence = !in_fence;
        }
        if in_fence {
            output.push_str(line);
            continue;
        }
        let mut rest = line;
        while let Some(start) = rest.find("](") {
            let target_start = start + 2;
            output.push_str(&rest[..target_start]);
            let Some(length) = rest[target_start..].find(')') else {
                rest = &rest[target_start..];
                continue;
            };
            let target = &rest[target_start..target_start + length];
            let rewritten = rewrite_target(page, directory, target)?;
            let local = !(rewritten.is_empty()
                || rewritten.contains("://")
                || rewritten.starts_with("mailto:")
                || rewritten.starts_with('/'));
            let file = rewritten.split('#').next().unwrap_or_default();
            if local && !docs.join(file).is_file() {
                return Err(format!(
                    "link {target} does not resolve to a file under docs/"
                ));
            }
            output.push_str(&rewritten);
            rest = &rest[target_start + length..];
        }
        output.push_str(rest);
    }
    Ok(output)
}

fn rewrite_target(page: &str, directory: &Path, target: &str) -> Result<String, String> {
    if target.is_empty()
        || target.contains("://")
        || target.starts_with("mailto:")
        || target.starts_with('/')
    {
        return Ok(target.to_string());
    }
    if target.starts_with('#') {
        return Ok(format!("{page}{target}"));
    }
    let (path, anchor) = target
        .split_once('#')
        .map_or((target, None), |(path, anchor)| (path, Some(anchor)));
    let mut resolved = PathBuf::new();
    for component in directory.join(path).components() {
        match component {
            Component::ParentDir => {
                if !resolved.pop() {
                    return Err(format!("link {target} leaves docs/"));
                }
            }
            Component::Normal(part) => resolved.push(part),
            _ => {}
        }
    }
    let resolved = resolved.to_string_lossy().replace('\\', "/");
    Ok(match anchor {
        Some(anchor) => format!("{resolved}#{anchor}"),
        None => resolved,
    })
}
