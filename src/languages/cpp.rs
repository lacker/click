//! The pinned semantic C++ frontend boundary.
//!
//! C++ source is interpreted by the repository-owned LibTooling exporter.
//! This module validates and locks that typed output; it deliberately does not
//! feed C++ text or generated C through the C parser.

mod import;
mod schema;

pub use import::{PreparedCppImport, load_import, refresh_import};
pub use schema::{
    CppBinaryOperator, CppExport, CppExpression, CppFunction, CppPlace, CppPlaceReference,
    CppProfile, CppSpan, CppStatement, CppType,
};
