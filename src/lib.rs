mod core;
mod reader;

pub use core::{
    ClickResult, Object, Symbol, Term, apply, empty_env, eval, eval_in_env, eval_state, halt,
    initial_state, lambda, r#match, parse, parse_many, return_state, set, step, var,
};

/// Parse one or more Click terms from source, evaluate each term independently,
/// and return the final value if any term was present.
pub fn run_source(source: &str) -> ClickResult<Option<Term>> {
    let mut result = None;
    for term in parse_many(source)? {
        result = Some(eval(&term)?);
    }
    Ok(result)
}
