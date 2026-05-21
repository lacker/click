mod core;
mod reader;

pub use core::{
    ClickResult, Object, Symbol, Term, apply, cek_evals_to_claim, cek_next_proof, cek_return_proof,
    cek_step, cek_step_equals_claim, cek_step_proof, check, closure, continue_state, empty_env,
    eval, eval_in_env, eval_state, halt, initial_state, lambda, object_equal_claim,
    object_equal_proof, parse, parse_many, step, var,
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
