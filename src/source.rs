//! Source-file positions shared by Surface Click and program languages.

use std::{fmt, sync::Arc};

/// The compiler source location associated with an imported physical line.
///
/// Preprocessed output does not preserve a meaningful macro-expanded column,
/// so imports retain the original file and line only.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SourceOrigin {
    pub filename: Arc<str>,
    pub line: usize,
}

/// A one-based line and column in a source file.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SourcePosition {
    pub line: usize,
    pub column: usize,
    pub origin: Option<Arc<SourceOrigin>>,
}

impl SourcePosition {
    pub fn new(line: usize, column: usize) -> Self {
        Self {
            line,
            column,
            origin: None,
        }
    }

    pub(crate) fn with_origin(
        line: usize,
        column: usize,
        filename: Arc<str>,
        original_line: usize,
    ) -> Self {
        Self {
            line,
            column,
            origin: Some(Arc::new(SourceOrigin {
                filename,
                line: original_line,
            })),
        }
    }
}

impl fmt::Display for SourcePosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.origin {
            Some(origin) => write!(f, "{}:{}", origin.filename, origin.line),
            None => write!(f, "line {}, column {}", self.line, self.column),
        }
    }
}

/// Maps every character index of `source` to its one-based line and column.
pub(crate) fn character_positions(source: &str) -> Vec<SourcePosition> {
    let mut positions = Vec::with_capacity(source.chars().count());
    let mut line = 1;
    let mut column = 1;
    for ch in source.chars() {
        positions.push(SourcePosition::new(line, column));
        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    positions
}
