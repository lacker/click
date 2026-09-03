//! Source-bundle utilities for the C0 frontend.
//!
//! This is deliberately a small include resolver, not a C preprocessor. It
//! expands supplied project-local headers and rejects all other preprocessor
//! directives so the C0 parser never silently verifies a different program.

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

/// Returns the normalized project-local headers directly included by a source.
/// System headers and all other preprocessor directives are rejected.
pub fn local_include_paths(source_path: &str, source: &str) -> Result<Vec<String>, CSourceError> {
    let mut includes = Vec::new();
    let mut in_block_comment = false;
    for (index, line) in source.lines().enumerate() {
        if let Some(include) = parse_directive(source_path, index + 1, line, &mut in_block_comment)?
        {
            includes.push(resolve_include_path(source_path, index + 1, include)?);
        }
    }
    Ok(includes)
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
    let mut expanded = String::new();
    expand_source(
        root_path,
        root_source,
        sources,
        &mut stack,
        &mut dependencies,
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
    expanded: &mut String,
) -> Result<(), CSourceError> {
    stack.push(source_path.to_string());
    let mut in_block_comment = false;
    for (index, line) in source.lines().enumerate() {
        let line_number = index + 1;
        let Some(include) = parse_directive(source_path, line_number, line, &mut in_block_comment)?
        else {
            expanded.push_str(line);
            expanded.push('\n');
            continue;
        };
        let included_path = resolve_include_path(source_path, line_number, include)?;
        if let Some(cycle_start) = stack.iter().position(|path| path == &included_path) {
            let mut cycle = stack[cycle_start..].to_vec();
            cycle.push(included_path);
            return Err(CSourceError::new(
                source_path,
                line_number,
                format!("include cycle: {}", cycle.join(" -> ")),
            ));
        }
        let included_source = lookup_source(sources, &included_path).ok_or_else(|| {
            CSourceError::new(
                source_path,
                line_number,
                format!(
                    "cannot resolve local include `{}` as `{included_path}` in the source bundle",
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
            expanded,
        )?;
    }
    stack.pop();
    Ok(())
}

fn parse_directive<'a>(
    source_path: &str,
    line_number: usize,
    line: &'a str,
    in_block_comment: &mut bool,
) -> Result<Option<&'a str>, CSourceError> {
    let Some(directive) = directive_text(line, in_block_comment) else {
        return Ok(None);
    };
    let directive = directive.trim_start();
    let Some(rest) = directive.strip_prefix("include") else {
        return Err(CSourceError::new(
            source_path,
            line_number,
            format!("unsupported preprocessor directive `#{directive}`"),
        ));
    };
    if !rest.is_empty() && !rest.chars().next().is_some_and(char::is_whitespace) {
        return Err(CSourceError::new(
            source_path,
            line_number,
            format!("unsupported preprocessor directive `#{directive}`"),
        ));
    }
    let rest = rest.trim_start();
    let Some(rest) = rest.strip_prefix('"') else {
        if rest.starts_with('<') {
            return Err(CSourceError::new(
                source_path,
                line_number,
                "system header includes are not supported yet; use a quoted project-local header",
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
    if include.is_empty() || !rest[end + 1..].trim().is_empty() {
        return Err(CSourceError::new(
            source_path,
            line_number,
            "malformed include; expected only a quoted header path",
        ));
    }
    Ok(Some(include))
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
        let cases = [
            ("#define VALUE 1\n", "unsupported preprocessor directive"),
            (
                "#include <stdint.h>\n",
                "system header includes are not supported",
            ),
        ];
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
