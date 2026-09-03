//! Source-bundle utilities for the C0 frontend.
//!
//! This is deliberately a small source expander, not a general C preprocessor.
//! It expands supplied project-local headers, a narrow literal-only macro
//! subset, and rejects all other preprocessor directives so the C0 parser
//! never silently verifies a different program.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Component, Path};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CSourceError {
    path: String,
    line: usize,
    message: String,
}

impl CSourceError {
    fn new(path: &str, line: usize, message: impl Into<String>) -> Self {
        Self {
            path: path.to_string(),
            line,
            message: message.into(),
        }
    }
}

impl fmt::Display for CSourceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}:{}: {}", self.path, self.line, self.message)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpandedCSource {
    source: String,
    dependencies: BTreeSet<String>,
}

impl ExpandedCSource {
    pub fn source(&self) -> &str {
        &self.source
    }

    pub fn dependencies(&self) -> &BTreeSet<String> {
        &self.dependencies
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SourceDirective {
    Include(String),
    SystemInclude(String),
    HeaderGuardStart(String),
    HeaderGuardDefine(String),
    MacroDefinition { name: String, value: String },
    HeaderGuardEnd,
    PragmaOnce,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceAnalysis {
    directives: BTreeMap<usize, SourceDirective>,
    includes: Vec<String>,
    guarded: bool,
    pragma_once: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SignificantLine {
    Code,
    Directive(SourceDirective),
}

/// Returns the normalized project-local headers directly included by a source.
/// Unsupported system headers and preprocessor directives are rejected. The
/// supported literal-only object-like macro definitions are accepted.
pub fn local_include_paths(source_path: &str, source: &str) -> Result<Vec<String>, CSourceError> {
    Ok(analyze_source(source_path, source)?.includes)
}

/// Expands all project-local quoted includes reachable from `root_path`.
/// `sources` contains the complete named source bundle, including headers.
pub fn expand_includes<'a>(
    root_path: &str,
    sources: &BTreeMap<&'a str, &'a str>,
) -> Result<ExpandedCSource, CSourceError> {
    let root_source = lookup_source(sources, root_path).ok_or_else(|| {
        CSourceError::new(
            root_path,
            1,
            "root source is not present in the source bundle",
        )
    })?;
    let mut dependencies = BTreeSet::new();
    let mut stack = Vec::new();
    let mut expanded_once = BTreeSet::new();
    let mut macros = BTreeMap::new();
    let mut expanded = String::new();
    expand_source(
        root_path,
        root_source,
        sources,
        &mut stack,
        &mut dependencies,
        &mut expanded_once,
        &mut macros,
        None,
        &mut expanded,
    )?;
    Ok(ExpandedCSource {
        source: expanded,
        dependencies,
    })
}

fn expand_source<'a>(
    source_path: &str,
    source: &str,
    sources: &BTreeMap<&'a str, &'a str>,
    stack: &mut Vec<String>,
    dependencies: &mut BTreeSet<String>,
    expanded_once: &mut BTreeSet<String>,
    macros: &mut BTreeMap<String, String>,
    include_site: Option<(&str, usize)>,
    expanded: &mut String,
) -> Result<(), CSourceError> {
    let analysis = analyze_source(source_path, source)?;
    let expands_once = analysis.guarded || analysis.pragma_once;
    if expands_once && !expanded_once.insert(source_path.to_string()) {
        return Ok(());
    }
    if let Some(cycle_start) = stack.iter().position(|path| path == source_path) {
        let mut cycle = stack[cycle_start..].to_vec();
        cycle.push(source_path.to_string());
        let (error_path, error_line) = include_site.unwrap_or((source_path, 1));
        return Err(CSourceError::new(
            error_path,
            error_line,
            format!("include cycle: {}", cycle.join(" -> ")),
        ));
    }
    stack.push(source_path.to_string());
    let mut macro_block_comment = false;
    for (index, line) in source.lines().enumerate() {
        let line_number = index + 1;
        let Some(directive) = analysis.directives.get(&line_number) else {
            expanded.push_str(&expand_macros_in_line(
                line,
                macros,
                &mut macro_block_comment,
            ));
            expanded.push('\n');
            continue;
        };
        match directive {
            SourceDirective::Include(include) => {
                let included_path = resolve_include_path(source_path, line_number, include)?;
                let included_source = lookup_source(sources, &included_path).ok_or_else(|| {
                    CSourceError::new(
                        source_path,
                        line_number,
                        format!(
                            "cannot resolve local include `{}` as {included_path} in the source bundle",
                            include
                        ),
                    )
                })?;
                dependencies.insert(included_path.clone());
                expand_source(
                    &included_path,
                    included_source,
                    sources,
                    stack,
                    dependencies,
                    expanded_once,
                    macros,
                    Some((source_path, line_number)),
                    expanded,
                )?;
            }
            SourceDirective::SystemInclude(_) => {}
            SourceDirective::MacroDefinition { name, value } => {
                if macros.insert(name.clone(), value.clone()).is_some() {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        format!("macro `{name}` is redefined"),
                    ));
                }
                // Keep a line for the removed directive so source positions in
                // the following C code remain aligned with the original file.
                expanded.push('\n');
            }
            SourceDirective::HeaderGuardStart(_)
            | SourceDirective::HeaderGuardDefine(_)
            | SourceDirective::HeaderGuardEnd
            | SourceDirective::PragmaOnce => {}
        }
    }
    stack.pop();
    Ok(())
}

fn analyze_source(source_path: &str, source: &str) -> Result<SourceAnalysis, CSourceError> {
    let mut directives = BTreeMap::new();
    let mut includes = Vec::new();
    let mut significant = Vec::new();
    let mut directive_comments = false;
    let mut content_comments = false;

    for (index, line) in source.lines().enumerate() {
        let line_number = index + 1;
        let has_code = line_has_non_comment_content(line, &mut content_comments);
        let directive = parse_directive(source_path, line_number, line, &mut directive_comments)?;
        if let Some(directive) = directive {
            if let SourceDirective::Include(include) = &directive {
                includes.push(resolve_include_path(source_path, line_number, include)?);
            }
            significant.push(SignificantLine::Directive(directive.clone()));
            directives.insert(line_number, directive);
        } else if has_code {
            significant.push(SignificantLine::Code);
        }
    }

    let framing: Vec<&SignificantLine> = significant
        .iter()
        .filter(|line| {
            !matches!(
                line,
                SignificantLine::Directive(SourceDirective::PragmaOnce)
            )
        })
        .collect();
    let guard_starts: Vec<&str> = framing
        .iter()
        .filter_map(|line| match line {
            SignificantLine::Directive(SourceDirective::HeaderGuardStart(name)) => {
                Some(name.as_str())
            }
            _ => None,
        })
        .collect();
    let guard_defines: Vec<&str> = framing
        .iter()
        .filter_map(|line| match line {
            SignificantLine::Directive(SourceDirective::HeaderGuardDefine(name)) => {
                Some(name.as_str())
            }
            _ => None,
        })
        .collect();
    let guard_ends = framing
        .iter()
        .filter(|line| {
            matches!(
                line,
                SignificantLine::Directive(SourceDirective::HeaderGuardEnd)
            )
        })
        .count();
    let has_guard_directive =
        !guard_starts.is_empty() || !guard_defines.is_empty() || guard_ends > 0;
    let valid_guard = guard_starts.len() == 1
        && guard_defines.len() == 1
        && guard_ends == 1
        && framing.len() >= 3
        && matches!(
            framing[0],
            SignificantLine::Directive(SourceDirective::HeaderGuardStart(_))
        )
        && matches!(
            framing[1],
            SignificantLine::Directive(SourceDirective::HeaderGuardDefine(_))
        )
        && matches!(
            framing.last(),
            Some(SignificantLine::Directive(SourceDirective::HeaderGuardEnd))
        )
        && guard_starts[0] == guard_defines[0];
    if has_guard_directive && !valid_guard {
        return Err(CSourceError::new(
            source_path,
            first_guard_line(&directives).unwrap_or(1),
            "only whole-header guards are supported; expected `#ifndef NAME`, `#define NAME`, and a final `#endif`",
        ));
    }

    Ok(SourceAnalysis {
        directives,
        includes,
        guarded: valid_guard,
        pragma_once: significant.iter().any(|line| {
            matches!(
                line,
                SignificantLine::Directive(SourceDirective::PragmaOnce)
            )
        }),
    })
}

fn first_guard_line(directives: &BTreeMap<usize, SourceDirective>) -> Option<usize> {
    directives.iter().find_map(|(line, directive)| {
        matches!(
            directive,
            SourceDirective::HeaderGuardStart(_)
                | SourceDirective::HeaderGuardDefine(_)
                | SourceDirective::HeaderGuardEnd
        )
        .then_some(*line)
    })
}

fn parse_directive<'a>(
    source_path: &str,
    line_number: usize,
    line: &'a str,
    in_block_comment: &mut bool,
) -> Result<Option<SourceDirective>, CSourceError> {
    let Some(directive) = directive_text(line, in_block_comment) else {
        return Ok(None);
    };
    let directive = directive.trim_start();
    if let Some(rest) = directive.strip_prefix("include")
        && (rest.is_empty() || rest.chars().next().is_some_and(char::is_whitespace))
    {
        let rest = rest.trim_start();
        let Some(rest) = rest.strip_prefix('"') else {
            if rest.starts_with('<') {
                let Some(end) = rest.find('>') else {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        "malformed system include; missing closing `>`",
                    ));
                };
                let header = &rest[1..end];
                if header == "stdint.h" && trailing_comments_only(&rest[end + 1..]) {
                    return Ok(Some(SourceDirective::SystemInclude(header.to_string())));
                }
                return Err(CSourceError::new(
                    source_path,
                    line_number,
                    format!(
                        "system header `<{header}>` is not supported; only `<stdint.h>` is modeled"
                    ),
                ));
            }
            return Err(CSourceError::new(
                source_path,
                line_number,
                "malformed include; expected a quoted project-local header",
            ));
        };
        let Some(end) = rest.find('"') else {
            return Err(CSourceError::new(
                source_path,
                line_number,
                "malformed include; missing closing quote",
            ));
        };
        let include = &rest[..end];
        if include.is_empty() || !trailing_comments_only(&rest[end + 1..]) {
            return Err(CSourceError::new(
                source_path,
                line_number,
                "malformed include; expected only a quoted header path",
            ));
        }
        return Ok(Some(SourceDirective::Include(include.to_string())));
    }
    if let Some(rest) = directive.strip_prefix("ifndef")
        && (rest.is_empty() || rest.chars().next().is_some_and(char::is_whitespace))
    {
        let (name, trailing) = split_identifier(rest.trim_start());
        if let Some(name) = name.filter(|_| trailing_comments_only(trailing)) {
            return Ok(Some(SourceDirective::HeaderGuardStart(name)));
        }
        return Err(CSourceError::new(
            source_path,
            line_number,
            "malformed header guard; expected `#ifndef NAME`",
        ));
    }
    if let Some(rest) = directive.strip_prefix("define")
        && (rest.is_empty() || rest.chars().next().is_some_and(char::is_whitespace))
    {
        let (name, trailing) = split_identifier(rest.trim_start());
        let Some(name) = name else {
            return Err(CSourceError::new(
                source_path,
                line_number,
                "malformed macro definition; expected `#define NAME VALUE`",
            ));
        };
        if trailing.starts_with('(') {
            return Err(CSourceError::new(
                source_path,
                line_number,
                "function-like macros are not supported; use an object-like literal macro",
            ));
        }
        if trailing_comments_only(trailing) {
            return Ok(Some(SourceDirective::HeaderGuardDefine(name)));
        }
        if let Some(value) = parse_macro_literal(trailing.trim_start()) {
            return Ok(Some(SourceDirective::MacroDefinition { name, value }));
        }
        return Err(CSourceError::new(
            source_path,
            line_number,
            format!(
                "unsupported macro definition `#{directive}`; expected one integer or character literal"
            ),
        ));
    }
    if directive == "endif"
        || directive
            .strip_prefix("endif")
            .is_some_and(trailing_comments_only)
    {
        return Ok(Some(SourceDirective::HeaderGuardEnd));
    }
    if directive == "pragma once"
        || directive
            .strip_prefix("pragma once")
            .is_some_and(trailing_comments_only)
    {
        return Ok(Some(SourceDirective::PragmaOnce));
    }
    Err(CSourceError::new(
        source_path,
        line_number,
        format!("unsupported preprocessor directive `#{directive}`"),
    ))
}

fn parse_macro_literal(input: &str) -> Option<String> {
    let input = input.trim_start();
    let end = if input.starts_with('\'') {
        macro_character_literal_end(input)?
    } else {
        macro_integer_literal_end(input)?
    };
    let (literal, trailing) = input.split_at(end);
    trailing_comments_only(trailing).then(|| literal.to_string())
}

fn macro_integer_literal_end(input: &str) -> Option<usize> {
    let bytes = input.as_bytes();
    let mut end = if bytes.first() == Some(&b'0') && matches!(bytes.get(1), Some(b'x') | Some(b'X'))
    {
        2
    } else if bytes.first().is_some_and(u8::is_ascii_digit) {
        1
    } else {
        return None;
    };
    let digit_end = end;
    if digit_end == 2 {
        while bytes.get(end).is_some_and(u8::is_ascii_hexdigit) {
            end += 1;
        }
        if end == digit_end {
            return None;
        }
    } else {
        while bytes.get(end).is_some_and(u8::is_ascii_digit) {
            end += 1;
        }
    }
    let suffix_start = end;
    while bytes.get(end).is_some_and(u8::is_ascii_alphabetic) {
        end += 1;
    }
    let suffix = input[suffix_start..end].to_ascii_lowercase();
    if !matches!(
        suffix.as_str(),
        "" | "u" | "l" | "ll" | "ul" | "lu" | "ull" | "llu"
    ) {
        return None;
    }
    if digit_end == 1 && input.starts_with('0') && end > 2 {
        let digits = &input[1..suffix_start];
        if digits.bytes().any(|digit| !(b'0'..=b'7').contains(&digit)) {
            return None;
        }
    }
    Some(end)
}

fn macro_character_literal_end(input: &str) -> Option<usize> {
    let chars = input.char_indices().collect::<Vec<_>>();
    let (_, first) = chars.get(1).copied()?;
    let quote_index = if first == '\\' {
        let (_, escaped) = chars.get(2).copied()?;
        if !matches!(escaped, 'n' | 'r' | 't' | '0' | '\\' | '\'' | '"') {
            return None;
        }
        3
    } else {
        if !first.is_ascii() || first == '\'' || first == '\n' {
            return None;
        }
        2
    };
    let (end, quote) = chars.get(quote_index).copied()?;
    (quote == '\'').then_some(end + quote.len_utf8())
}

fn expand_macros_in_line(
    line: &str,
    macros: &BTreeMap<String, String>,
    in_block_comment: &mut bool,
) -> String {
    let chars = line.chars().collect::<Vec<_>>();
    let mut expanded = String::with_capacity(line.len());
    let mut index = 0;
    while index < chars.len() {
        if *in_block_comment {
            let start = index;
            while index + 1 < chars.len() && !(chars[index] == '*' && chars[index + 1] == '/') {
                index += 1;
            }
            if index + 1 == chars.len() {
                expanded.extend(chars[start..].iter().copied());
                return expanded;
            }
            index += 2;
            expanded.extend(chars[start..index].iter().copied());
            *in_block_comment = false;
            continue;
        }
        if chars[index] == '/' && chars.get(index + 1) == Some(&'/') {
            expanded.extend(chars[index..].iter().copied());
            break;
        }
        if chars[index] == '/' && chars.get(index + 1) == Some(&'*') {
            let start = index;
            index += 2;
            *in_block_comment = true;
            expanded.extend(chars[start..index].iter().copied());
            continue;
        }
        if chars[index] == '\'' || chars[index] == '"' {
            let start = index;
            index = quoted_literal_end(&chars, index, chars[index]);
            expanded.extend(chars[start..index].iter().copied());
            continue;
        }
        if is_identifier_start(chars[index]) {
            let start = index;
            index += 1;
            while index < chars.len() && is_identifier_continue(chars[index]) {
                index += 1;
            }
            let name = chars[start..index].iter().collect::<String>();
            if let Some(value) = macros.get(&name) {
                expanded.push_str(value);
            } else {
                expanded.extend(chars[start..index].iter().copied());
            }
            continue;
        }
        expanded.push(chars[index]);
        index += 1;
    }
    expanded
}

fn quoted_literal_end(chars: &[char], start: usize, quote: char) -> usize {
    let mut index = start + 1;
    while index < chars.len() {
        if chars[index] == '\\' {
            index += 2;
        } else if chars[index] == quote {
            return index + 1;
        } else {
            index += 1;
        }
    }
    chars.len()
}

fn is_identifier_start(character: char) -> bool {
    character == '_' || character.is_ascii_alphabetic()
}

fn is_identifier_continue(character: char) -> bool {
    character == '_' || character.is_ascii_alphanumeric()
}

fn split_identifier(input: &str) -> (Option<String>, &str) {
    let mut end = 0;
    for (index, character) in input.char_indices() {
        let valid = if index == 0 {
            character == '_' || character.is_ascii_alphabetic()
        } else {
            character == '_' || character.is_ascii_alphanumeric()
        };
        if !valid {
            break;
        }
        end = index + character.len_utf8();
    }
    if end == 0 {
        (None, input)
    } else {
        (Some(input[..end].to_string()), &input[end..])
    }
}

fn trailing_comments_only(mut input: &str) -> bool {
    loop {
        input = input.trim_start();
        if input.is_empty() || input.starts_with("//") {
            return true;
        }
        if let Some(rest) = input.strip_prefix("/*") {
            let Some(end) = rest.find("*/") else {
                return false;
            };
            input = &rest[end + 2..];
            continue;
        }
        return false;
    }
}

fn line_has_non_comment_content(line: &str, in_block_comment: &mut bool) -> bool {
    let bytes = line.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        if *in_block_comment {
            if let Some(end) = line[index..].find("*/") {
                index += end + 2;
                *in_block_comment = false;
            } else {
                return false;
            }
        } else if line[index..].starts_with("//") {
            return false;
        } else if line[index..].starts_with("/*") {
            *in_block_comment = true;
            index += 2;
        } else if bytes[index].is_ascii_whitespace() {
            index += 1;
        } else {
            return true;
        }
    }
    false
}

fn directive_text<'a>(line: &'a str, in_block_comment: &mut bool) -> Option<&'a str> {
    let bytes = line.as_bytes();
    let mut index = 0;
    loop {
        while index < bytes.len() && bytes[index].is_ascii_whitespace() {
            index += 1;
        }
        if *in_block_comment {
            let closing = line[index..].find("*/")?;
            index += closing + 2;
            *in_block_comment = false;
            continue;
        }
        if line[index..].starts_with("//") {
            return None;
        }
        if line[index..].starts_with("/*") {
            *in_block_comment = true;
            index += 2;
            continue;
        }
        return line[index..].strip_prefix('#').map(str::trim_start);
    }
}

fn resolve_include_path(
    source_path: &str,
    line_number: usize,
    include: &str,
) -> Result<String, CSourceError> {
    if Path::new(include).is_absolute() {
        return Err(CSourceError::new(
            source_path,
            line_number,
            "absolute header paths are not supported",
        ));
    }
    let parent = Path::new(source_path)
        .parent()
        .unwrap_or_else(|| Path::new(""));
    let mut components = Vec::new();
    for component in parent.components().chain(Path::new(include).components()) {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                if components.last().is_some_and(|part| part != "..") {
                    components.pop();
                } else {
                    components.push("..".to_string());
                }
            }
            Component::Normal(part) => components.push(part.to_string_lossy().into_owned()),
            Component::RootDir | Component::Prefix(_) => {
                return Err(CSourceError::new(
                    source_path,
                    line_number,
                    "absolute header paths are not supported",
                ));
            }
        }
    }
    Ok(components.join("/"))
}

fn lookup_source<'a>(sources: &BTreeMap<&'a str, &'a str>, source_path: &str) -> Option<&'a str> {
    sources.get(source_path).copied().or_else(|| {
        sources.iter().find_map(|(candidate, source)| {
            let normalized = normalize_path(candidate);
            (normalized == source_path).then_some(*source)
        })
    })
}

fn normalize_path(path: &str) -> String {
    let mut components = Vec::new();
    for component in Path::new(path).components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                if components.last().is_some_and(|part| part != "..") {
                    components.pop();
                } else {
                    components.push("..".to_string());
                }
            }
            Component::Normal(part) => components.push(part.to_string_lossy().into_owned()),
            Component::RootDir | Component::Prefix(_) => {}
        }
    }
    components.join("/")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_include_paths_resolve_relative_to_including_file() {
        assert_eq!(
            local_include_paths("src/main.c", "#include \"../include/types.h\"\n").unwrap(),
            ["include/types.h"]
        );
    }

    #[test]
    fn include_expansion_collects_transitive_headers() {
        let sources = BTreeMap::from([
            (
                "src/main.c",
                "#include \"../include/types.h\"\nint32 main() { return 0; }\n",
            ),
            (
                "include/types.h",
                "#include \"common.h\"\nstruct pair { int32 value; };\n",
            ),
            ("include/common.h", "typedef int32 index_t;\n"),
        ]);
        let expanded = expand_includes("src/main.c", &sources).unwrap();
        assert!(expanded.source().contains("typedef int32 index_t;"));
        assert!(expanded.source().contains("struct pair { int32 value; };"));
        assert_eq!(
            expanded.dependencies(),
            &BTreeSet::from([
                "include/common.h".to_string(),
                "include/types.h".to_string()
            ])
        );
    }

    #[test]
    fn guarded_headers_expand_only_once_through_a_diamond() {
        let sources = BTreeMap::from([
            ("main.c", "#include \"left.h\"\n#include \"right.h\"\n"),
            (
                "left.h",
                "#ifndef LEFT_H\n#define LEFT_H\n#include \"common.h\"\ntypedef int32 left_t;\n#endif\n",
            ),
            (
                "right.h",
                "#ifndef RIGHT_H\n#define RIGHT_H\n#include \"common.h\"\ntypedef int32 right_t;\n#endif\n",
            ),
            (
                "common.h",
                "#ifndef COMMON_H\n#define COMMON_H\ntypedef int32 shared_t;\n#endif\n",
            ),
        ]);
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert_eq!(
            expanded.source().matches("typedef int32 shared_t;").count(),
            1
        );
        assert_eq!(
            expanded.source().matches("typedef int32 left_t;").count(),
            1
        );
        assert_eq!(
            expanded.source().matches("typedef int32 right_t;").count(),
            1
        );
    }

    #[test]
    fn pragma_once_headers_expand_only_once() {
        let sources = BTreeMap::from([
            ("main.c", "#include \"left.h\"\n#include \"right.h\"\n"),
            ("left.h", "#include \"common.h\"\n"),
            ("right.h", "#include \"common.h\"\n"),
            ("common.h", "#pragma once\ntypedef int32 shared_t;\n"),
        ]);
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert_eq!(
            expanded.source().matches("typedef int32 shared_t;").count(),
            1
        );
    }

    #[test]
    fn modeled_system_headers_are_ignored_during_expansion() {
        let sources = BTreeMap::from([(
            "main.c",
            "#include <stdint.h>\nint32_t run(uint8_t value) { return value; }\n",
        )]);
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert!(!expanded.source().contains("#include <stdint.h>"));
        assert!(expanded.source().contains("int32_t run(uint8_t value)"));
        assert!(expanded.dependencies().is_empty());
        assert!(
            local_include_paths("main.c", sources["main.c"])
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn literal_macros_expand_across_headers_without_touching_comments_or_literals() {
        let sources = BTreeMap::from([
            (
                "main.c",
                "#include \"config.h\"\nint32 run(int32 value) { return value + LIMIT; }\n",
            ),
            (
                "config.h",
                "#ifndef CONFIG_H\n#define CONFIG_H\n#define LIMIT 4\n#define MARKER '\\0'\n#endif\n",
            ),
        ]);
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert!(expanded.source().contains("return value + 4;"));
        assert!(!expanded.source().contains("#define LIMIT"));

        let source = "#define LIMIT 4\nint32 run() { /* LIMIT */ return LIMIT + '\\0'; }\n";
        let expanded = expand_includes("main.c", &BTreeMap::from([("main.c", source)])).unwrap();
        assert!(
            expanded
                .source()
                .contains("int32 run() { /* LIMIT */ return 4 + '\\0'; }")
        );
    }

    #[test]
    fn literal_macro_redefinitions_and_nonliteral_replacements_are_rejected() {
        let redefined = BTreeMap::from([(
            "main.c",
            "#define LIMIT 4\n#define LIMIT 5\nint32 run() { return LIMIT; }\n",
        )]);
        let error = expand_includes("main.c", &redefined).unwrap_err();
        assert!(error.to_string().contains("macro `LIMIT` is redefined"));

        let cases = [
            ("#define LIMIT (1 + 2)\n", "unsupported macro definition"),
            (
                "#define LIMIT(value) value\n",
                "function-like macros are not supported",
            ),
        ];
        for (source, expected) in cases {
            let error = local_include_paths("main.c", source).unwrap_err();
            assert!(error.to_string().contains(expected));
        }
    }

    #[test]
    fn malformed_header_guards_are_rejected_but_arbitrary_conditionals_remain_unsupported() {
        let mismatched = BTreeMap::from([(
            "bad.h",
            "#ifndef BAD_H\n#define OTHER_H\ntypedef int32 value_t;\n#endif\n",
        )]);
        let error = local_include_paths("bad.h", mismatched["bad.h"]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("only whole-header guards are supported")
        );

        let conditional = BTreeMap::from([("bad.h", "#if defined(BAD_H)\n#endif\n")]);
        let error = local_include_paths("bad.h", conditional["bad.h"]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("unsupported preprocessor directive `#if defined(BAD_H)`")
        );
    }

    #[test]
    fn include_expansion_reports_missing_headers_and_cycles() {
        let missing = BTreeMap::from([("main.c", "#include \"missing.h\"\n")]);
        let error = expand_includes("main.c", &missing).unwrap_err();
        assert!(error.to_string().contains("cannot resolve local include"));

        let cycle = BTreeMap::from([
            ("main.c", "#include \"a.h\"\n"),
            ("a.h", "#include \"b.h\"\n"),
            ("b.h", "#include \"a.h\"\n"),
        ]);
        let error = expand_includes("main.c", &cycle).unwrap_err();
        assert!(error.to_string().contains("include cycle"));
    }

    #[test]
    fn unsupported_preprocessor_directives_are_rejected() {
        let cases = [(
            "#include <stdio.h>\n",
            "system header `<stdio.h>` is not supported",
        )];
        for (source, expected) in cases {
            let error = local_include_paths("main.c", source).unwrap_err();
            assert!(error.to_string().contains(expected));
        }
    }

    #[test]
    fn comments_do_not_turn_text_into_preprocessor_directives() {
        let source = "/*\n#include \"missing.h\"\n*/\n// #include \"missing.h\"\n";
        assert!(local_include_paths("main.c", source).unwrap().is_empty());
    }
}
