mod core;
mod reader;

pub use core::{
    ClickResult, Object, Symbol, Term, apply, cek_step, check, closure, continue_state, empty_env,
    equal, equal_claim, equal_structural_proof, eval, eval_in_env, eval_state, get, halt, has,
    if_expr, initial_state, lambda, parse, parse_many, quote, returns_claim, returns_next_proof,
    returns_return_proof, step, step_equals_claim, step_proof, var, with,
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
