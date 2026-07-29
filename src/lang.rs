//! Source-language front ends for the kernel.

use std::fmt;

pub mod c;
pub mod click;

/// A one-based line and column in a source file.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SourcePosition {
    pub line: usize,
    pub column: usize,
}

impl SourcePosition {
    pub fn new(line: usize, column: usize) -> Self {
        Self { line, column }
    }
}

impl fmt::Display for SourcePosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}, column {}", self.line, self.column)
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
