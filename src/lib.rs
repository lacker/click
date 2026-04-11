pub mod foundation;
pub mod kernel;
mod reader;

pub use foundation::{Context, Declaration, declare, run_source};
pub use kernel::{ClickResult, Name, NameMap, StepResult, Symbol, SymbolMap, Term, step, type_of};
