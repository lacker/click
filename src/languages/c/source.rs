//! Source-bundle utilities for the C0 frontend.
//!
//! This is deliberately a small source expander, not a general C preprocessor.
//! It expands supplied project-local headers, a narrow literal-only macro
//! subset, a bounded one-parameter function-like macro subset, a bounded
//! conditional-compilation subset, and rejects all other preprocessor
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

#[derive(Clone, Debug, Eq, PartialEq)]
enum SourceDirective {
    Include(String),
    SystemInclude(String),
    HeaderGuardDefine(String),
    MacroDefinition {
        name: String,
        definition: MacroDefinition,
    },
    MacroUndefine(String),
    ConditionalStart(Conditional),
    ConditionalElif(Conditional),
    ConditionalElse,
    ConditionalEnd,
    PragmaOnce,
    Unsupported(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum MacroDefinition {
    ObjectLike(String),
    FunctionLike {
        parameter: String,
        replacement: String,
    },
}

impl MacroDefinition {
    fn object_value(&self) -> Option<&str> {
        match self {
            Self::ObjectLike(value) => Some(value),
            Self::FunctionLike { .. } => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Conditional {
    Literal(bool),
    ValueLiteral(String),
    Macro(String),
    Ifdef(String),
    Ifndef(String),
    Defined(String),
    Not(Box<Conditional>),
    And(Box<Conditional>, Box<Conditional>),
    Or(Box<Conditional>, Box<Conditional>),
    Comparison {
        left: Box<Conditional>,
        operator: ComparisonOperator,
        right: Box<Conditional>,
    },
    Unsupported(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ComparisonOperator {
    Equal,
    NotEqual,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceAnalysis {
    directives: BTreeMap<usize, SourceDirective>,
    header_guard_define_line: Option<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SignificantLine {
    Code,
    Directive(SourceDirective),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConditionalTruth {
    True,
    False,
    Unknown,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ConditionalFrame {
    parent_active: ConditionalTruth,
    branch_taken: ConditionalTruth,
    else_seen: bool,
}

/// Returns the normalized project-local headers directly included by a source.
/// Unsupported system headers and preprocessor directives are rejected. The
/// supported object-like and one-parameter function-like macro definitions are
/// accepted.
pub fn local_include_paths(source_path: &str, source: &str) -> Result<Vec<String>, CSourceError> {
    let analysis = analyze_source(source_path, source)?;
    collect_local_include_paths(source_path, &analysis)
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
    let mut defined_macros = BTreeSet::new();
    let mut expanded = String::new();
    expand_source(
        root_path,
        root_source,
        sources,
        &mut stack,
        &mut dependencies,
        &mut expanded_once,
        &mut macros,
        &mut defined_macros,
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
    macros: &mut BTreeMap<String, MacroDefinition>,
    defined_macros: &mut BTreeSet<String>,
    include_site: Option<(&str, usize)>,
    expanded: &mut String,
) -> Result<(), CSourceError> {
    let analysis = analyze_source(source_path, source)?;
    if expanded_once.contains(source_path) {
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
    let mut conditional_stack = Vec::new();
    let mut active = ConditionalTruth::True;
    for (index, line) in source.lines().enumerate() {
        let line_number = index + 1;
        let Some(directive) = analysis.directives.get(&line_number) else {
            if active != ConditionalTruth::False {
                let expanded_line =
                    expand_macros_in_line(line, macros, &mut macro_block_comment)
                        .map_err(|message| CSourceError::new(source_path, line_number, message))?;
                expanded.push_str(&expanded_line);
            }
            expanded.push('\n');
            continue;
        };
        match directive {
            SourceDirective::ConditionalStart(condition) => {
                if active != ConditionalTruth::False
                    && let Conditional::Unsupported(expression) = condition
                {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        unsupported_condition_message(expression),
                    ));
                }
                let condition_active = if active == ConditionalTruth::False {
                    ConditionalTruth::False
                } else {
                    evaluate_condition(condition, "if", macros, defined_macros)
                        .map_err(|message| CSourceError::new(source_path, line_number, message))?
                };
                conditional_stack.push(ConditionalFrame {
                    parent_active: active,
                    branch_taken: condition_active,
                    else_seen: false,
                });
                active = and_truth(active, condition_active);
                expanded.push('\n');
            }
            SourceDirective::ConditionalElif(condition) => {
                let Some(frame) = conditional_stack.last_mut() else {
                    unreachable!("analyze_source validates conditional structure")
                };
                let previous_branch_taken = frame.branch_taken;
                let condition_active = if frame.parent_active == ConditionalTruth::False
                    || previous_branch_taken == ConditionalTruth::True
                {
                    ConditionalTruth::False
                } else if let Conditional::Unsupported(expression) = condition {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        unsupported_condition_message(expression),
                    ));
                } else {
                    evaluate_condition(condition, "elif", macros, defined_macros)
                        .map_err(|message| CSourceError::new(source_path, line_number, message))?
                };
                let branch_active =
                    and_truth(negate_truth(previous_branch_taken), condition_active);
                frame.branch_taken = or_truth(previous_branch_taken, condition_active);
                active = and_truth(frame.parent_active, branch_active);
                expanded.push('\n');
            }
            SourceDirective::ConditionalElse => {
                let Some(frame) = conditional_stack.last_mut() else {
                    unreachable!("analyze_source validates conditional structure")
                };
                frame.else_seen = true;
                active = and_truth(frame.parent_active, negate_truth(frame.branch_taken));
                expanded.push('\n');
            }
            SourceDirective::ConditionalEnd => {
                let Some(frame) = conditional_stack.pop() else {
                    unreachable!("analyze_source validates conditional structure")
                };
                active = frame.parent_active;
                expanded.push('\n');
            }
            SourceDirective::Include(include) if active != ConditionalTruth::False => {
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
                    defined_macros,
                    Some((source_path, line_number)),
                    expanded,
                )?;
            }
            SourceDirective::Include(_) => expanded.push('\n'),
            SourceDirective::SystemInclude(header) if active != ConditionalTruth::False => {
                if header != "stdint.h" {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        format!(
                            "system header `<{header}>` is not supported; only `<stdint.h>` is modeled"
                        ),
                    ));
                }
                expanded.push('\n');
            }
            SourceDirective::SystemInclude(_) => expanded.push('\n'),
            SourceDirective::MacroDefinition { name, definition }
                if active != ConditionalTruth::False =>
            {
                if !defined_macros.insert(name.clone()) {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        format!("macro `{name}` is redefined"),
                    ));
                }
                macros.insert(name.clone(), definition.clone());
                // Keep a line for the removed directive so source positions in
                // the following C code remain aligned with the original file.
                expanded.push('\n');
            }
            SourceDirective::MacroDefinition { .. } => expanded.push('\n'),
            SourceDirective::MacroUndefine(name) if active != ConditionalTruth::False => {
                defined_macros.remove(name);
                macros.remove(name);
                expanded.push('\n');
            }
            SourceDirective::MacroUndefine(_) => expanded.push('\n'),
            SourceDirective::HeaderGuardDefine(name) if active != ConditionalTruth::False => {
                if analysis.header_guard_define_line != Some(line_number) {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        "only whole-header guards are supported; valueless `#define` is not supported here",
                    ));
                }
                if !defined_macros.insert(name.clone()) {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        format!("macro `{name}` is redefined"),
                    ));
                }
                expanded.push('\n');
            }
            SourceDirective::HeaderGuardDefine(_) => expanded.push('\n'),
            SourceDirective::PragmaOnce if active != ConditionalTruth::False => {
                expanded_once.insert(source_path.to_string());
                expanded.push('\n');
            }
            SourceDirective::PragmaOnce => expanded.push('\n'),
            SourceDirective::Unsupported(message) if active != ConditionalTruth::False => {
                return Err(CSourceError::new(source_path, line_number, message));
            }
            SourceDirective::Unsupported(_) => expanded.push('\n'),
        }
    }
    debug_assert!(conditional_stack.is_empty());
    stack.pop();
    Ok(())
}

fn collect_local_include_paths(
    source_path: &str,
    analysis: &SourceAnalysis,
) -> Result<Vec<String>, CSourceError> {
    let mut includes = Vec::new();
    let mut macros = BTreeMap::new();
    let mut defined_macros = BTreeSet::new();
    let mut conditional_stack = Vec::new();
    let mut active = ConditionalTruth::True;
    let mut may_have_external_macros = false;
    for (&line_number, directive) in &analysis.directives {
        match directive {
            SourceDirective::ConditionalStart(condition) => {
                if active != ConditionalTruth::False
                    && let Conditional::Unsupported(expression) = condition
                {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        unsupported_condition_message(expression),
                    ));
                }
                let condition_active = if active == ConditionalTruth::False {
                    ConditionalTruth::False
                } else {
                    evaluate_condition_for_discovery(
                        condition,
                        &macros,
                        &defined_macros,
                        may_have_external_macros,
                    )
                };
                conditional_stack.push(ConditionalFrame {
                    parent_active: active,
                    branch_taken: condition_active,
                    else_seen: false,
                });
                active = and_truth(active, condition_active);
            }
            SourceDirective::ConditionalElif(condition) => {
                let Some(frame) = conditional_stack.last_mut() else {
                    unreachable!("analyze_source validates conditional structure")
                };
                let previous_branch_taken = frame.branch_taken;
                let condition_active = if frame.parent_active == ConditionalTruth::False
                    || previous_branch_taken == ConditionalTruth::True
                {
                    ConditionalTruth::False
                } else if let Conditional::Unsupported(expression) = condition {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        unsupported_condition_message(expression),
                    ));
                } else {
                    evaluate_condition_for_discovery(
                        condition,
                        &macros,
                        &defined_macros,
                        may_have_external_macros,
                    )
                };
                let branch_active =
                    and_truth(negate_truth(previous_branch_taken), condition_active);
                frame.branch_taken = or_truth(previous_branch_taken, condition_active);
                active = and_truth(frame.parent_active, branch_active);
            }
            SourceDirective::ConditionalElse => {
                let Some(frame) = conditional_stack.last_mut() else {
                    unreachable!("analyze_source validates conditional structure")
                };
                frame.else_seen = true;
                active = and_truth(frame.parent_active, negate_truth(frame.branch_taken));
            }
            SourceDirective::ConditionalEnd => {
                let Some(frame) = conditional_stack.pop() else {
                    unreachable!("analyze_source validates conditional structure")
                };
                active = frame.parent_active;
            }
            SourceDirective::Include(include) if active != ConditionalTruth::False => {
                if active == ConditionalTruth::True {
                    may_have_external_macros = true;
                }
                includes.push(resolve_include_path(source_path, line_number, include)?);
            }
            SourceDirective::Include(_) => {}
            SourceDirective::SystemInclude(header) if active != ConditionalTruth::False => {
                if header != "stdint.h" {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        format!(
                            "system header `<{header}>` is not supported; only `<stdint.h>` is modeled"
                        ),
                    ));
                }
            }
            SourceDirective::SystemInclude(_) => {}
            SourceDirective::MacroDefinition { name, definition }
                if active == ConditionalTruth::True =>
            {
                if defined_macros.insert(name.clone()) {
                    macros.insert(name.clone(), definition.clone());
                } else {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        format!("macro `{name}` is redefined"),
                    ));
                }
            }
            SourceDirective::MacroDefinition { .. } => {}
            SourceDirective::MacroUndefine(name) if active != ConditionalTruth::False => {
                defined_macros.remove(name);
                macros.remove(name);
            }
            SourceDirective::MacroUndefine(_) => {}
            SourceDirective::HeaderGuardDefine(name) if active == ConditionalTruth::True => {
                if analysis.header_guard_define_line != Some(line_number) {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        "only whole-header guards are supported; valueless `#define` is not supported here",
                    ));
                }
                defined_macros.insert(name.clone());
            }
            SourceDirective::HeaderGuardDefine(_) => {}
            SourceDirective::PragmaOnce => {}
            SourceDirective::Unsupported(message) if active != ConditionalTruth::False => {
                return Err(CSourceError::new(source_path, line_number, message));
            }
            SourceDirective::Unsupported(_) => {}
        }
    }
    debug_assert!(conditional_stack.is_empty());
    Ok(includes)
}

fn evaluate_condition(
    condition: &Conditional,
    directive_name: &str,
    macros: &BTreeMap<String, MacroDefinition>,
    defined_macros: &BTreeSet<String>,
) -> Result<ConditionalTruth, String> {
    match condition {
        Conditional::Literal(value) => Ok(if *value {
            ConditionalTruth::True
        } else {
            ConditionalTruth::False
        }),
        Conditional::ValueLiteral(value) => Err(format!(
            "unsupported conditional expression `#{directive_name} {value}`; expected `0` or `1`, or a supported comparison"
        )),
        Conditional::Macro(name) => {
            let Some(value) = macros.get(name).and_then(MacroDefinition::object_value) else {
                return Err(format!(
                    "unsupported conditional expression `#{directive_name} {name}`; expected a previously defined literal macro"
                ));
            };
            macro_condition_truth(value).ok_or_else(|| {
                format!(
                    "unsupported conditional expression `#{directive_name} {name}`; expected `{name}` to be defined as 0 or 1"
                )
            })
        }
        Conditional::Ifdef(name) => Ok(if defined_macros.contains(name) {
            ConditionalTruth::True
        } else {
            ConditionalTruth::False
        }),
        Conditional::Ifndef(name) => Ok(if defined_macros.contains(name) {
            ConditionalTruth::False
        } else {
            ConditionalTruth::True
        }),
        Conditional::Defined(name) => Ok(if defined_macros.contains(name) {
            ConditionalTruth::True
        } else {
            ConditionalTruth::False
        }),
        Conditional::Not(condition) => {
            evaluate_condition(condition, directive_name, macros, defined_macros).map(negate_truth)
        }
        Conditional::And(left, right) => {
            let left = evaluate_condition(left, directive_name, macros, defined_macros)?;
            if left == ConditionalTruth::False {
                Ok(ConditionalTruth::False)
            } else {
                let right = evaluate_condition(right, directive_name, macros, defined_macros)?;
                Ok(and_truth(left, right))
            }
        }
        Conditional::Or(left, right) => {
            let left = evaluate_condition(left, directive_name, macros, defined_macros)?;
            if left == ConditionalTruth::True {
                Ok(ConditionalTruth::True)
            } else {
                let right = evaluate_condition(right, directive_name, macros, defined_macros)?;
                Ok(or_truth(left, right))
            }
        }
        Conditional::Comparison {
            left,
            operator,
            right,
        } => {
            let left = evaluate_comparison_operand(left, directive_name, macros, defined_macros)?;
            let right = evaluate_comparison_operand(right, directive_name, macros, defined_macros)?;
            Ok(compare_values(left, *operator, right))
        }
        Conditional::Unsupported(expression) => Err(unsupported_condition_message(expression)),
    }
}

fn unsupported_condition_message(expression: &str) -> String {
    format!(
        "unsupported conditional expression `#{expression}`; expected bounded `#if` atoms combined with `!`, `&&`, `||`, or parentheses"
    )
}

fn evaluate_condition_for_discovery(
    condition: &Conditional,
    macros: &BTreeMap<String, MacroDefinition>,
    defined_macros: &BTreeSet<String>,
    may_have_external_macros: bool,
) -> ConditionalTruth {
    match condition {
        Conditional::Literal(value) => {
            if *value {
                ConditionalTruth::True
            } else {
                ConditionalTruth::False
            }
        }
        Conditional::ValueLiteral(_) => ConditionalTruth::Unknown,
        Conditional::Macro(name) => macros
            .get(name)
            .and_then(MacroDefinition::object_value)
            .and_then(|value| macro_condition_truth(value))
            .unwrap_or(ConditionalTruth::Unknown),
        Conditional::Ifdef(name) => {
            if defined_macros.contains(name) {
                ConditionalTruth::True
            } else if may_have_external_macros {
                ConditionalTruth::Unknown
            } else {
                ConditionalTruth::False
            }
        }
        Conditional::Ifndef(name) => {
            if defined_macros.contains(name) {
                ConditionalTruth::False
            } else if may_have_external_macros {
                ConditionalTruth::Unknown
            } else {
                ConditionalTruth::True
            }
        }
        Conditional::Defined(name) => {
            if defined_macros.contains(name) {
                ConditionalTruth::True
            } else if may_have_external_macros {
                ConditionalTruth::Unknown
            } else {
                ConditionalTruth::False
            }
        }
        Conditional::Not(condition) => negate_truth(evaluate_condition_for_discovery(
            condition,
            macros,
            defined_macros,
            may_have_external_macros,
        )),
        Conditional::And(left, right) => {
            let left = evaluate_condition_for_discovery(
                left,
                macros,
                defined_macros,
                may_have_external_macros,
            );
            if left == ConditionalTruth::False {
                ConditionalTruth::False
            } else {
                let right = evaluate_condition_for_discovery(
                    right,
                    macros,
                    defined_macros,
                    may_have_external_macros,
                );
                and_truth(left, right)
            }
        }
        Conditional::Or(left, right) => {
            let left = evaluate_condition_for_discovery(
                left,
                macros,
                defined_macros,
                may_have_external_macros,
            );
            if left == ConditionalTruth::True {
                ConditionalTruth::True
            } else {
                let right = evaluate_condition_for_discovery(
                    right,
                    macros,
                    defined_macros,
                    may_have_external_macros,
                );
                or_truth(left, right)
            }
        }
        Conditional::Comparison {
            left,
            operator,
            right,
        } => {
            let Some(left) = comparison_operand_for_discovery(
                left,
                macros,
                defined_macros,
                may_have_external_macros,
            ) else {
                return ConditionalTruth::Unknown;
            };
            let Some(right) = comparison_operand_for_discovery(
                right,
                macros,
                defined_macros,
                may_have_external_macros,
            ) else {
                return ConditionalTruth::Unknown;
            };
            compare_values(left, *operator, right)
        }
        Conditional::Unsupported(_) => ConditionalTruth::Unknown,
    }
}

fn evaluate_comparison_operand(
    condition: &Conditional,
    directive_name: &str,
    macros: &BTreeMap<String, MacroDefinition>,
    defined_macros: &BTreeSet<String>,
) -> Result<u64, String> {
    match condition {
        Conditional::Literal(value) => Ok(u64::from(*value)),
        Conditional::ValueLiteral(value) => preprocessor_literal_value(value).ok_or_else(|| {
            format!(
                "unsupported conditional expression `#{directive_name}`; expected integer or character literal operands"
            )
        }),
        Conditional::Macro(name) => {
            let Some(value) = macros.get(name).and_then(MacroDefinition::object_value) else {
                return Err(format!(
                    "unsupported conditional expression `#{directive_name}`; expected `{name}` to be a previously defined literal macro"
                ));
            };
            preprocessor_literal_value(value).ok_or_else(|| {
                format!(
                    "unsupported conditional expression `#{directive_name}`; expected `{name}` to be defined as one integer or character literal"
                )
            })
        }
        Conditional::Defined(name) => Ok(u64::from(defined_macros.contains(name))),
        _ => Err(format!(
            "unsupported conditional expression `#{directive_name}`; comparison operands must be literal values or macro names"
        )),
    }
}

fn comparison_operand_for_discovery(
    condition: &Conditional,
    macros: &BTreeMap<String, MacroDefinition>,
    defined_macros: &BTreeSet<String>,
    may_have_external_macros: bool,
) -> Option<u64> {
    match condition {
        Conditional::Literal(value) => Some(u64::from(*value)),
        Conditional::ValueLiteral(value) => preprocessor_literal_value(value),
        Conditional::Macro(name) => macros
            .get(name)
            .and_then(MacroDefinition::object_value)
            .and_then(|value| preprocessor_literal_value(value)),
        Conditional::Defined(name) => {
            if defined_macros.contains(name) {
                Some(1)
            } else if may_have_external_macros {
                None
            } else {
                Some(0)
            }
        }
        _ => None,
    }
}

fn compare_values(left: u64, operator: ComparisonOperator, right: u64) -> ConditionalTruth {
    let equal = left == right;
    match operator {
        ComparisonOperator::Equal if equal => ConditionalTruth::True,
        ComparisonOperator::Equal => ConditionalTruth::False,
        ComparisonOperator::NotEqual if equal => ConditionalTruth::False,
        ComparisonOperator::NotEqual => ConditionalTruth::True,
    }
}

fn macro_condition_truth(value: &str) -> Option<ConditionalTruth> {
    match value {
        "0" => Some(ConditionalTruth::False),
        "1" => Some(ConditionalTruth::True),
        _ => None,
    }
}

fn and_truth(left: ConditionalTruth, right: ConditionalTruth) -> ConditionalTruth {
    match (left, right) {
        (ConditionalTruth::False, _) | (_, ConditionalTruth::False) => ConditionalTruth::False,
        (ConditionalTruth::True, ConditionalTruth::True) => ConditionalTruth::True,
        _ => ConditionalTruth::Unknown,
    }
}

fn or_truth(left: ConditionalTruth, right: ConditionalTruth) -> ConditionalTruth {
    match (left, right) {
        (ConditionalTruth::True, _) | (_, ConditionalTruth::True) => ConditionalTruth::True,
        (ConditionalTruth::False, ConditionalTruth::False) => ConditionalTruth::False,
        _ => ConditionalTruth::Unknown,
    }
}

fn negate_truth(value: ConditionalTruth) -> ConditionalTruth {
    match value {
        ConditionalTruth::True => ConditionalTruth::False,
        ConditionalTruth::False => ConditionalTruth::True,
        ConditionalTruth::Unknown => ConditionalTruth::Unknown,
    }
}

fn analyze_source(source_path: &str, source: &str) -> Result<SourceAnalysis, CSourceError> {
    let mut directives = BTreeMap::new();
    let mut significant = Vec::new();
    let mut directive_comments = false;
    let mut content_comments = false;

    for (index, line) in source.lines().enumerate() {
        let line_number = index + 1;
        let has_code = line_has_non_comment_content(line, &mut content_comments);
        let directive = parse_directive(source_path, line_number, line, &mut directive_comments)?;
        if let Some(directive) = directive {
            significant.push(SignificantLine::Directive(directive.clone()));
            directives.insert(line_number, directive);
        } else if has_code {
            significant.push(SignificantLine::Code);
        }
    }
    validate_conditional_structure(source_path, &directives)?;

    let framing: Vec<&SignificantLine> = significant
        .iter()
        .filter(|line| {
            !matches!(
                line,
                SignificantLine::Directive(SourceDirective::PragmaOnce)
            )
        })
        .collect();
    let header_guard_define_line = header_guard_shape(&framing, &directives);

    Ok(SourceAnalysis {
        directives,
        header_guard_define_line,
    })
}

fn validate_conditional_structure(
    source_path: &str,
    directives: &BTreeMap<usize, SourceDirective>,
) -> Result<(), CSourceError> {
    let mut stack = Vec::new();
    for (&line_number, directive) in directives {
        match directive {
            SourceDirective::ConditionalStart(_) => stack.push((line_number, false)),
            SourceDirective::ConditionalElif(_) => {
                let Some((_, else_seen)) = stack.last() else {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        "unmatched `#elif`; expected an open conditional",
                    ));
                };
                if *else_seen {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        "`#elif` after `#else` is not supported",
                    ));
                }
            }
            SourceDirective::ConditionalElse => {
                let Some((_, else_seen)) = stack.last_mut() else {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        "unmatched `#else`; expected an open conditional",
                    ));
                };
                if *else_seen {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        "multiple `#else` directives are not supported in one conditional",
                    ));
                }
                *else_seen = true;
            }
            SourceDirective::ConditionalEnd => {
                if stack.pop().is_none() {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        "unmatched `#endif`; expected an open conditional",
                    ));
                }
            }
            _ => {}
        }
    }
    if let Some((line_number, _)) = stack.last() {
        return Err(CSourceError::new(
            source_path,
            *line_number,
            "unterminated conditional; expected `#endif`",
        ));
    }
    Ok(())
}

fn header_guard_shape(
    framing: &[&SignificantLine],
    directives: &BTreeMap<usize, SourceDirective>,
) -> Option<usize> {
    let valid = framing.len() >= 3
        && matches!(
            framing[0],
            SignificantLine::Directive(SourceDirective::ConditionalStart(Conditional::Ifndef(_)))
        )
        && matches!(
            framing[1],
            SignificantLine::Directive(SourceDirective::HeaderGuardDefine(_))
        )
        && matches!(
            framing.last(),
            Some(SignificantLine::Directive(SourceDirective::ConditionalEnd))
        )
        && match (framing[0], framing[1]) {
            (
                SignificantLine::Directive(SourceDirective::ConditionalStart(Conditional::Ifndef(
                    start,
                ))),
                SignificantLine::Directive(SourceDirective::HeaderGuardDefine(define)),
            ) => start == define,
            _ => false,
        };
    if !valid {
        return None;
    }
    let define_line = directives.iter().find_map(|(line, directive)| {
        matches!(directive, SourceDirective::HeaderGuardDefine(_)).then_some(*line)
    });
    define_line
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
                if !trailing_comments_only(&rest[end + 1..]) {
                    return Err(CSourceError::new(
                        source_path,
                        line_number,
                        "malformed system include; expected only a header name",
                    ));
                }
                return Ok(Some(SourceDirective::Unsupported(format!(
                    "system header `<{header}>` is not supported; only `<stdint.h>` is modeled"
                ))));
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
            return Ok(Some(SourceDirective::ConditionalStart(
                Conditional::Ifndef(name),
            )));
        }
        return Err(CSourceError::new(
            source_path,
            line_number,
            "malformed header guard; expected `#ifndef NAME`",
        ));
    }
    if let Some(rest) = directive.strip_prefix("ifdef")
        && (rest.is_empty() || rest.chars().next().is_some_and(char::is_whitespace))
    {
        let (name, trailing) = split_identifier(rest.trim_start());
        if let Some(name) = name.filter(|_| trailing_comments_only(trailing)) {
            return Ok(Some(SourceDirective::ConditionalStart(Conditional::Ifdef(
                name,
            ))));
        }
        return Err(CSourceError::new(
            source_path,
            line_number,
            "malformed conditional; expected `#ifdef NAME`",
        ));
    }
    if let Some(rest) = directive.strip_prefix("if")
        && (rest.is_empty() || rest.chars().next().is_some_and(char::is_whitespace))
    {
        return Ok(Some(SourceDirective::ConditionalStart(parse_condition(
            "if", rest,
        ))));
    }
    if let Some(rest) = directive.strip_prefix("elif")
        && (rest.is_empty() || rest.chars().next().is_some_and(char::is_whitespace))
    {
        return Ok(Some(SourceDirective::ConditionalElif(parse_condition(
            "elif", rest,
        ))));
    }
    if let Some(rest) = directive.strip_prefix("define")
        && (rest.is_empty() || rest.chars().next().is_some_and(char::is_whitespace))
    {
        let (name, trailing) = split_identifier(rest.trim_start());
        let Some(name) = name else {
            return Ok(Some(SourceDirective::Unsupported(
                "malformed macro definition; expected `#define NAME VALUE`".to_string(),
            )));
        };
        if trailing.starts_with('(') {
            return Ok(Some(match parse_function_macro_definition(trailing) {
                Ok(definition) => SourceDirective::MacroDefinition { name, definition },
                Err(message) => SourceDirective::Unsupported(message.to_string()),
            }));
        }
        if trailing_comments_only(trailing) {
            return Ok(Some(SourceDirective::HeaderGuardDefine(name)));
        }
        if let Some(value) = parse_macro_literal(trailing.trim_start()) {
            return Ok(Some(SourceDirective::MacroDefinition {
                name,
                definition: MacroDefinition::ObjectLike(value),
            }));
        }
        return Ok(Some(SourceDirective::Unsupported(format!(
            "unsupported macro definition `#{directive}`; expected one integer or character literal"
        ))));
    }
    if let Some(rest) = directive.strip_prefix("undef")
        && (rest.is_empty() || rest.chars().next().is_some_and(char::is_whitespace))
    {
        let (name, trailing) = split_identifier(rest.trim_start());
        if let Some(name) = name.filter(|_| trailing_comments_only(trailing)) {
            return Ok(Some(SourceDirective::MacroUndefine(name)));
        }
        return Ok(Some(SourceDirective::Unsupported(
            "malformed macro undefinition; expected `#undef NAME`".to_string(),
        )));
    }
    if directive
        .strip_prefix("else")
        .is_some_and(trailing_comments_only)
    {
        return Ok(Some(SourceDirective::ConditionalElse));
    }
    if directive == "endif"
        || directive
            .strip_prefix("endif")
            .is_some_and(trailing_comments_only)
    {
        return Ok(Some(SourceDirective::ConditionalEnd));
    }
    if directive == "pragma once"
        || directive
            .strip_prefix("pragma once")
            .is_some_and(trailing_comments_only)
    {
        return Ok(Some(SourceDirective::PragmaOnce));
    }
    Ok(Some(SourceDirective::Unsupported(format!(
        "unsupported preprocessor directive `#{directive}`"
    ))))
}

fn parse_condition(directive_name: &str, input: &str) -> Conditional {
    let rest = input.trim_start();
    let expression = rest.trim();
    let mut parser = ConditionalParser::new(rest);
    match parser.parse() {
        Ok(condition) if condition_is_supported(&condition) => condition,
        Err(()) => Conditional::Unsupported(format!("{directive_name} {expression}")),
        Ok(_) => Conditional::Unsupported(format!("{directive_name} {expression}")),
    }
}

fn condition_is_supported(condition: &Conditional) -> bool {
    match condition {
        Conditional::Literal(_)
        | Conditional::Macro(_)
        | Conditional::Ifdef(_)
        | Conditional::Ifndef(_)
        | Conditional::Defined(_) => true,
        Conditional::ValueLiteral(_) | Conditional::Unsupported(_) => false,
        Conditional::Not(condition) => condition_is_supported(condition),
        Conditional::And(left, right) | Conditional::Or(left, right) => {
            condition_is_supported(left) && condition_is_supported(right)
        }
        Conditional::Comparison {
            left,
            operator: _,
            right,
        } => comparison_operand_is_supported(left) && comparison_operand_is_supported(right),
    }
}

fn comparison_operand_is_supported(condition: &Conditional) -> bool {
    matches!(
        condition,
        Conditional::Literal(_)
            | Conditional::ValueLiteral(_)
            | Conditional::Macro(_)
            | Conditional::Defined(_)
    )
}

struct ConditionalParser<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> ConditionalParser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, position: 0 }
    }

    fn parse(&mut self) -> Result<Conditional, ()> {
        let condition = self.parse_or()?;
        self.skip_whitespace();
        trailing_comments_only(&self.input[self.position..])
            .then_some(condition)
            .ok_or(())
    }

    fn parse_or(&mut self) -> Result<Conditional, ()> {
        let mut condition = self.parse_and()?;
        loop {
            self.skip_whitespace();
            if !self.consume("||") {
                return Ok(condition);
            }
            let right = self.parse_and()?;
            condition = Conditional::Or(Box::new(condition), Box::new(right));
        }
    }

    fn parse_and(&mut self) -> Result<Conditional, ()> {
        let mut condition = self.parse_comparison()?;
        loop {
            self.skip_whitespace();
            if !self.consume("&&") {
                return Ok(condition);
            }
            let right = self.parse_comparison()?;
            condition = Conditional::And(Box::new(condition), Box::new(right));
        }
    }

    fn parse_comparison(&mut self) -> Result<Conditional, ()> {
        let left = self.parse_unary()?;
        self.skip_whitespace();
        let operator = if self.consume("==") {
            ComparisonOperator::Equal
        } else if self.consume("!=") {
            ComparisonOperator::NotEqual
        } else {
            return Ok(left);
        };
        let right = self.parse_unary()?;
        if !comparison_operand_is_supported(&left) || !comparison_operand_is_supported(&right) {
            return Err(());
        }
        Ok(Conditional::Comparison {
            left: Box::new(left),
            operator,
            right: Box::new(right),
        })
    }

    fn parse_unary(&mut self) -> Result<Conditional, ()> {
        self.skip_whitespace();
        if self.consume("!") {
            Ok(Conditional::Not(Box::new(self.parse_unary()?)))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<Conditional, ()> {
        self.skip_whitespace();
        if self.consume("(") {
            let condition = self.parse_or()?;
            self.skip_whitespace();
            if !self.consume(")") {
                return Err(());
            }
            Ok(condition)
        } else {
            self.parse_atom()
        }
    }

    fn parse_atom(&mut self) -> Result<Conditional, ()> {
        self.skip_whitespace();
        if let Some(literal) = self.parse_literal() {
            return Ok(match literal.as_str() {
                "0" => Conditional::Literal(false),
                "1" => Conditional::Literal(true),
                _ => Conditional::ValueLiteral(literal),
            });
        }
        let name = self.parse_identifier().ok_or(())?;
        if name != "defined" {
            return Ok(Conditional::Macro(name));
        }
        self.skip_whitespace();
        if !self.consume("(") {
            return Err(());
        }
        let name = self.parse_identifier().ok_or(())?;
        self.skip_whitespace();
        if !self.consume(")") {
            return Err(());
        }
        Ok(Conditional::Defined(name))
    }

    fn parse_literal(&mut self) -> Option<String> {
        let rest = &self.input[self.position..];
        let end = if rest.starts_with('\'') {
            macro_character_literal_end(rest)?
        } else {
            macro_integer_literal_end(rest)?
        };
        self.position += end;
        Some(rest[..end].to_string())
    }

    fn parse_identifier(&mut self) -> Option<String> {
        let rest = &self.input[self.position..];
        let (name, _) = split_identifier(rest);
        let name = name?;
        self.position += name.len();
        Some(name)
    }

    fn skip_whitespace(&mut self) {
        while let Some(character) = self.input[self.position..].chars().next() {
            if !character.is_ascii_whitespace() {
                break;
            }
            self.position += character.len_utf8();
        }
    }

    fn consume(&mut self, token: &str) -> bool {
        if self.input[self.position..].starts_with(token) {
            self.position += token.len();
            true
        } else {
            false
        }
    }
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

fn parse_function_macro_definition(input: &str) -> Result<MacroDefinition, &'static str> {
    let Some(close) = input.find(')') else {
        return Err(
            "malformed function-like macro; expected exactly one identifier parameter and a replacement",
        );
    };
    let parameters = input[1..close].trim();
    let (parameter, trailing) = split_identifier(parameters);
    let Some(parameter) = parameter.filter(|_| trailing_comments_only(trailing)) else {
        return Err("function-like macros currently support exactly one identifier parameter");
    };
    let replacement = input[close + 1..].trim_start();
    if replacement.contains('#') {
        return Err("function-like macro stringification and token pasting are not supported");
    }
    let replacement = if trailing_comments_only(replacement) {
        String::new()
    } else {
        replacement.trim_end().to_string()
    };
    Ok(MacroDefinition::FunctionLike {
        parameter,
        replacement,
    })
}

fn preprocessor_literal_value(literal: &str) -> Option<u64> {
    if literal.starts_with('\'') {
        return preprocessor_character_literal_value(literal);
    }
    let end = macro_integer_literal_end(literal)?;
    (end == literal.len()).then(|| preprocessor_integer_literal_value(literal, end))?
}

fn preprocessor_integer_literal_value(literal: &str, end: usize) -> Option<u64> {
    let bytes = literal.as_bytes();
    let (digit_start, radix, digit_end) = if bytes.starts_with(b"0x") || bytes.starts_with(b"0X") {
        let mut digit_end = 2;
        while bytes.get(digit_end).is_some_and(u8::is_ascii_hexdigit) {
            digit_end += 1;
        }
        (2, 16, digit_end)
    } else {
        let mut digit_end = 0;
        while bytes.get(digit_end).is_some_and(u8::is_ascii_digit) {
            digit_end += 1;
        }
        let radix = if digit_end > 1 && bytes.first() == Some(&b'0') {
            8
        } else {
            10
        };
        (0, radix, digit_end)
    };
    (digit_end <= end).then(|| u64::from_str_radix(&literal[digit_start..digit_end], radix).ok())?
}

fn preprocessor_character_literal_value(literal: &str) -> Option<u64> {
    let end = macro_character_literal_end(literal)?;
    if end != literal.len() {
        return None;
    }
    let chars = literal.chars().collect::<Vec<_>>();
    let value = if chars.get(1) == Some(&'\\') {
        match chars.get(2).copied()? {
            'n' => b'\n',
            'r' => b'\r',
            't' => b'\t',
            '0' => b'\0',
            '\\' => b'\\',
            '\'' => b'\'',
            '"' => b'"',
            _ => return None,
        }
    } else {
        chars
            .get(1)
            .copied()?
            .is_ascii()
            .then_some(chars[1] as u8)?
    };
    Some(u64::from(value))
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
    macros: &BTreeMap<String, MacroDefinition>,
    in_block_comment: &mut bool,
) -> Result<String, String> {
    let mut state = MacroExpansionState::default();
    expand_macro_text(line, macros, in_block_comment, &mut state)
}

#[derive(Default)]
struct MacroExpansionState {
    active: Vec<String>,
}

const MAX_MACRO_EXPANSION_DEPTH: usize = 64;

fn expand_macro_text(
    text: &str,
    macros: &BTreeMap<String, MacroDefinition>,
    in_block_comment: &mut bool,
    state: &mut MacroExpansionState,
) -> Result<String, String> {
    let chars = text.chars().collect::<Vec<_>>();
    let mut expanded = String::with_capacity(text.len());
    let mut index = 0;
    while index < chars.len() {
        if *in_block_comment {
            let start = index;
            while index + 1 < chars.len() && !(chars[index] == '*' && chars[index + 1] == '/') {
                index += 1;
            }
            if index + 1 == chars.len() {
                expanded.extend(chars[start..].iter().copied());
                return Ok(expanded);
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
            let Some(definition) = macros.get(&name).cloned() else {
                expanded.extend(chars[start..index].iter().copied());
                continue;
            };
            match definition {
                MacroDefinition::ObjectLike(value) => {
                    expanded.push_str(&expand_macro_replacement(&name, &value, macros, state)?);
                }
                MacroDefinition::FunctionLike {
                    parameter,
                    replacement,
                } if chars.get(index) == Some(&'(') => {
                    let (arguments, end) = parse_macro_arguments(&chars, index, &name)?;
                    expanded.push_str(&expand_function_macro(
                        &name,
                        &parameter,
                        &replacement,
                        &arguments,
                        macros,
                        state,
                    )?);
                    index = end;
                }
                MacroDefinition::FunctionLike { .. } => {
                    expanded.extend(chars[start..index].iter().copied());
                }
            }
            continue;
        }
        expanded.push(chars[index]);
        index += 1;
    }
    Ok(expanded)
}

fn expand_macro_replacement(
    name: &str,
    replacement: &str,
    macros: &BTreeMap<String, MacroDefinition>,
    state: &mut MacroExpansionState,
) -> Result<String, String> {
    enter_macro(name, state)?;
    let mut replacement_comments = false;
    let result = expand_macro_text(replacement, macros, &mut replacement_comments, state);
    state.active.pop();
    result
}

fn expand_function_macro(
    name: &str,
    parameter: &str,
    replacement: &str,
    arguments: &[String],
    macros: &BTreeMap<String, MacroDefinition>,
    state: &mut MacroExpansionState,
) -> Result<String, String> {
    if arguments.len() != 1 || arguments[0].trim().is_empty() {
        return Err(format!(
            "macro `{name}` expects exactly one non-empty argument"
        ));
    }
    let mut argument_comments = false;
    let argument = expand_macro_text(arguments[0].trim(), macros, &mut argument_comments, state)?;
    let substituted = substitute_macro_parameter(replacement, parameter, &argument);
    expand_macro_replacement(name, &substituted, macros, state)
}

fn enter_macro(name: &str, state: &mut MacroExpansionState) -> Result<(), String> {
    if state.active.iter().any(|active| active == name) {
        return Err(format!(
            "recursive macro expansion involving `{name}` is not supported"
        ));
    }
    if state.active.len() >= MAX_MACRO_EXPANSION_DEPTH {
        return Err(format!(
            "macro expansion exceeded the depth limit of {MAX_MACRO_EXPANSION_DEPTH}"
        ));
    }
    state.active.push(name.to_string());
    Ok(())
}

fn parse_macro_arguments(
    chars: &[char],
    open: usize,
    name: &str,
) -> Result<(Vec<String>, usize), String> {
    let mut arguments = Vec::new();
    let mut argument_start = open + 1;
    let mut nested_parentheses = 0;
    let mut index = open + 1;
    while index < chars.len() {
        if chars[index] == '\'' || chars[index] == '"' {
            index = quoted_literal_end(chars, index, chars[index]);
            continue;
        }
        if chars[index] == '/' && chars.get(index + 1) == Some(&'/') {
            return Err(format!(
                "unterminated invocation of function-like macro `{name}`"
            ));
        }
        if chars[index] == '/' && chars.get(index + 1) == Some(&'*') {
            index += 2;
            while index + 1 < chars.len() && !(chars[index] == '*' && chars[index + 1] == '/') {
                index += 1;
            }
            if index + 1 == chars.len() {
                return Err(format!(
                    "unterminated comment in invocation of function-like macro `{name}`"
                ));
            }
            index += 2;
            continue;
        }
        match chars[index] {
            '(' => nested_parentheses += 1,
            ')' if nested_parentheses == 0 => {
                arguments.push(chars[argument_start..index].iter().collect());
                return Ok((arguments, index + 1));
            }
            ')' => nested_parentheses -= 1,
            ',' if nested_parentheses == 0 => {
                arguments.push(chars[argument_start..index].iter().collect());
                argument_start = index + 1;
            }
            _ => {}
        }
        index += 1;
    }
    Err(format!(
        "unterminated invocation of function-like macro `{name}`"
    ))
}

fn substitute_macro_parameter(replacement: &str, parameter: &str, argument: &str) -> String {
    let chars = replacement.chars().collect::<Vec<_>>();
    let mut expanded = String::with_capacity(replacement.len());
    let mut index = 0;
    while index < chars.len() {
        if chars[index] == '/' && chars.get(index + 1) == Some(&'/') {
            expanded.extend(chars[index..].iter().copied());
            break;
        }
        if chars[index] == '/' && chars.get(index + 1) == Some(&'*') {
            let start = index;
            index += 2;
            while index + 1 < chars.len() && !(chars[index] == '*' && chars[index + 1] == '/') {
                index += 1;
            }
            if index + 1 < chars.len() {
                index += 2;
            } else {
                index = chars.len();
            }
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
            if name == parameter {
                expanded.push_str(argument);
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
                "#define LIMIT(left, right) left\n",
                "exactly one identifier parameter",
            ),
            (
                "#define LIMIT(value) #value\n",
                "stringification and token pasting are not supported",
            ),
        ];
        for (source, expected) in cases {
            let error = local_include_paths("main.c", source).unwrap_err();
            assert!(error.to_string().contains(expected));
        }
    }

    #[test]
    fn one_parameter_function_macros_expand_across_headers_and_nested_calls() {
        let sources = BTreeMap::from([
            (
                "main.c",
                r##"#include "macros.h"
int32 run(int32 value) { return APPLY(INCREMENT(value)); }
int32 nested(int32 value) { return TWICE(INCREMENT((value + value))); }
int32 preserved(int32 value) { /* APPLY(value) */ return value; }
"##,
            ),
            (
                "macros.h",
                r##"#ifndef MACROS_H
#define MACROS_H
#define INCREMENT(value) ((value) + 1)
#define TWICE(value) ((value) + (value))
#define APPLY(value) TWICE(value)
#endif
"##,
            ),
        ]);
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert!(
            expanded
                .source()
                .contains("int32 run(int32 value) { return ((((value) + 1)) + (((value) + 1))); }")
        );
        assert!(expanded.source().contains(
            "int32 nested(int32 value) { return (((((value + value)) + 1)) + ((((value + value)) + 1))); }"
        ));
        assert!(
            expanded
                .source()
                .contains("int32 preserved(int32 value) { /* APPLY(value) */ return value; }")
        );
        assert!(!expanded.source().contains("INCREMENT("));
        assert!(!expanded.source().contains("TWICE("));
        assert!(!expanded.source().contains("return APPLY("));
        assert!(expanded.dependencies().contains("macros.h"));
    }

    #[test]
    fn function_macro_invocations_report_arity_and_recursion_errors() {
        let too_many = BTreeMap::from([(
            "main.c",
            "#define WRAP(value) (value)\nint32 run() { return WRAP(1, 2); }\n",
        )]);
        let error = expand_includes("main.c", &too_many).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("macro `WRAP` expects exactly one non-empty argument")
        );

        let recursive = BTreeMap::from([(
            "main.c",
            "#define LOOP(value) LOOP(value)\nint32 run() { return LOOP(1); }\n",
        )]);
        let error = expand_includes("main.c", &recursive).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("recursive macro expansion involving `LOOP`")
        );
    }

    #[test]
    fn undefines_remove_macros_and_allow_later_redefinition() {
        let sources = BTreeMap::from([
            (
                "main.c",
                r##"#define FEATURE 0
#undef FEATURE
#ifdef FEATURE
int32 wrong(void) { return 0; }
#else
#define FEATURE 1
#if FEATURE
#include "config.h"
#endif
#endif
int32 run(void) { return VALUE; }
"##,
            ),
            ("config.h", "#define VALUE 4\n"),
        ]);
        assert_eq!(
            local_include_paths("main.c", sources["main.c"]).unwrap(),
            ["config.h"]
        );
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert!(expanded.source().contains("int32 run(void) { return 4; }"));
        assert!(!expanded.source().contains("wrong(void)"));

        let malformed = local_include_paths("main.c", "#undef\n").unwrap_err();
        assert!(
            malformed
                .to_string()
                .contains("malformed macro undefinition")
        );
    }

    #[test]
    fn undefining_a_header_guard_allows_a_later_include() {
        let sources = BTreeMap::from([
            (
                "main.c",
                "#include \"guard.h\"\n#undef GUARD_H\n#include \"guard.h\"\n",
            ),
            (
                "guard.h",
                "#ifndef GUARD_H\n#define GUARD_H\ntypedef int32 shared_t;\n#endif\n",
            ),
        ]);
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert_eq!(
            expanded.source().matches("typedef int32 shared_t;").count(),
            2
        );
    }

    #[test]
    fn bounded_conditionals_select_active_branches_and_ignore_inactive_includes() {
        let sources = BTreeMap::from([
            (
                "main.c",
                r##"#define FEATURE 1
#if 0
#include "missing.h"
#include <stdio.h>
#else
#ifdef FEATURE
#include "config.h"
#else
int32 wrong(void) { return 0; }
#endif
#endif
#if FEATURE
int32 run(void) { return VALUE; }
#else
int32 wrong_again(void) { return 0; }
#endif
"##,
            ),
            ("config.h", "#define VALUE 4\n"),
        ]);
        assert_eq!(
            local_include_paths("main.c", sources["main.c"]).unwrap(),
            ["config.h"]
        );
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert!(expanded.source().contains("int32 run(void) { return 4; }"));
        assert!(!expanded.source().contains("wrong(void)"));
        assert!(!expanded.source().contains("wrong_again(void)"));
        assert!(!expanded.source().contains("missing.h"));
        assert!(!expanded.source().contains("stdio.h"));
    }

    #[test]
    fn bounded_conditional_chains_select_the_first_true_branch() {
        let sources = BTreeMap::from([(
            "main.c",
            r##"#define FEATURE 0
#if FEATURE
int32 wrong_feature(void) { return 0; }
#elif 0
int32 wrong_literal(void) { return 0; }
#elif 1
int32 run(void) { return 7; }
#elif defined(SKIPPED)
#include "missing.h"
#else
int32 wrong_else(void) { return 0; }
#endif
"##,
        )]);
        assert!(
            local_include_paths("main.c", sources["main.c"])
                .unwrap()
                .is_empty()
        );
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert!(expanded.source().contains("int32 run(void) { return 7; }"));
        assert!(!expanded.source().contains("wrong_feature"));
        assert!(!expanded.source().contains("wrong_literal"));
        assert!(!expanded.source().contains("wrong_else"));
        assert!(!expanded.source().contains("missing.h"));
    }

    #[test]
    fn defined_conditions_follow_macro_state() {
        let sources = BTreeMap::from([(
            "main.c",
            r##"#define FEATURE 0
#if defined(FEATURE)
int32 defined_branch(void) { return 1; }
#else
int32 wrong_defined_branch(void) { return 0; }
#endif
#undef FEATURE
#if !defined(FEATURE)
int32 not_defined_branch(void) { return 2; }
#else
int32 wrong_not_defined_branch(void) { return 0; }
#endif
"##,
        )]);
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert!(expanded.source().contains("int32 defined_branch(void)"));
        assert!(expanded.source().contains("int32 not_defined_branch(void)"));
        assert!(!expanded.source().contains("wrong_defined_branch"));
        assert!(!expanded.source().contains("wrong_not_defined_branch"));
    }

    #[test]
    fn boolean_conditions_respect_precedence_and_short_circuit_includes() {
        let sources = BTreeMap::from([
            (
                "main.c",
                r##"#define FEATURE 1
#define DISABLED 0
#if defined(FEATURE) && FEATURE
#include "config.h"
#else
#include "missing.h"
#endif
#if !defined(MISSING) || DISABLED
int32 fallback(void) { return 5; }
#endif
#if (defined(FEATURE) && !defined(MISSING)) || DISABLED
int32 grouped(void) { return 6; }
#endif
#if 1 || 1 && 0
int32 precedence(void) { return 7; }
#else
int32 wrong_precedence(void) { return 0; }
#endif
#if 0 && defined(UNKNOWN)
#include "missing_again.h"
#endif
"##,
            ),
            ("config.h", "#define VALUE 4\n"),
        ]);
        assert_eq!(
            local_include_paths("main.c", sources["main.c"]).unwrap(),
            ["config.h"]
        );
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert!(expanded.source().contains("int32 fallback(void)"));
        assert!(expanded.source().contains("int32 grouped(void)"));
        assert!(expanded.source().contains("int32 precedence(void)"));
        assert!(!expanded.source().contains("wrong_precedence"));
        assert!(!expanded.source().contains("missing.h"));
        assert!(!expanded.source().contains("missing_again.h"));
    }

    #[test]
    fn equality_conditions_compare_literal_macros_and_short_circuit_includes() {
        let sources = BTreeMap::from([
            (
                "main.c",
                r##"#define FEATURE 1
#define DISABLED 0
#define HEX_FEATURE 0x01
#define NUL '\0'
#if FEATURE == 1
#include "config.h"
#else
#include "missing.h"
#endif
#if DISABLED != 1
int32 run(void) { return VALUE; }
#else
int32 wrong(void) { return 0; }
#endif
#if DISABLED == 1
int32 wrong_elif(void) { return 0; }
#elif FEATURE != 0
int32 elif_comparison(void) { return 8; }
#else
int32 wrong_elif_else(void) { return 0; }
#endif
#if HEX_FEATURE == 1 && NUL == 0
int32 literal_forms(void) { return VALUE; }
#endif
#if 0 == 1 || FEATURE != 0
int32 boolean_comparison(void) { return 7; }
#endif
"##,
            ),
            ("config.h", "#define VALUE 4\n"),
        ]);
        assert_eq!(
            local_include_paths("main.c", sources["main.c"]).unwrap(),
            ["config.h"]
        );
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert!(expanded.source().contains("int32 run(void) { return 4; }"));
        assert!(
            expanded
                .source()
                .contains("int32 elif_comparison(void) { return 8; }")
        );
        assert!(
            expanded
                .source()
                .contains("int32 literal_forms(void) { return 4; }")
        );
        assert!(
            expanded
                .source()
                .contains("int32 boolean_comparison(void) { return 7; }")
        );
        assert!(!expanded.source().contains("wrong(void)"));
        assert!(!expanded.source().contains("wrong_elif"));
        assert!(!expanded.source().contains("missing.h"));
    }

    #[test]
    fn defined_conditions_accept_bounded_whitespace_and_elif_forms() {
        let sources = BTreeMap::from([(
            "main.c",
            r##"#if 0
int32 wrong(void) { return 0; }
#elif ! defined (MISSING) /* explanatory comment */
int32 run(void) { return 3; }
#endif
"##,
        )]);
        assert!(
            local_include_paths("main.c", sources["main.c"])
                .unwrap()
                .is_empty()
        );
        let expanded = expand_includes("main.c", &sources).unwrap();
        assert!(expanded.source().contains("int32 run(void) { return 3; }"));
        assert!(!expanded.source().contains("wrong(void)"));
    }

    #[test]
    fn conditionals_require_balanced_structure_and_supported_active_conditions() {
        let cases = [
            ("#else\n", "unmatched `#else`"),
            ("#elif 1\n", "unmatched `#elif`"),
            ("#if 1\n#else\n#else\n#endif\n", "multiple `#else`"),
            ("#if 0\n#else\n#elif 1\n#endif\n", "`#elif` after `#else`"),
            ("#if 1\n", "unterminated conditional"),
            (
                "#if FEATURE + 1 == 2\n#endif\n",
                "unsupported conditional expression `#if FEATURE + 1 == 2`",
            ),
        ];
        for (source, expected) in cases {
            let error = local_include_paths("main.c", source).unwrap_err();
            assert!(error.to_string().contains(expected), "{error}");
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

        let conditional = BTreeMap::from([("bad.h", "#if BAD_H + 1 == 2\n#endif\n")]);
        let error = local_include_paths("bad.h", conditional["bad.h"]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("unsupported conditional expression `#if BAD_H + 1 == 2`")
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
