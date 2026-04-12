pub mod foundation;
pub mod kernel;
mod reader;

pub use foundation::{Context, Declaration, declare, run_source};
pub use kernel::{ClickResult, Name, NameMap, Symbol, SymbolMap, Term, step, type_of};
