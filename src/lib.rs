mod core;
mod reader;

pub use core::{
    ClickResult, Context, Object, Symbol, Term, and_claim, and_intro_proof, and_left_proof,
    and_right_proof, apply, cek_step, check, check_in_context, closure, continue_state,
    empty_context, empty_env, equal, equal_claim, equal_structural_proof, eval, eval_in_env,
    eval_state, exists_claim, exists_elim_proof, exists_intro_proof, false_claim, false_elim_proof,
    forall_claim, forall_elim_proof, forall_intro_proof, get, halt, has, if_expr, implies_claim,
    implies_elim_proof, implies_intro_proof, initial_state, lambda, logic_var, not_claim,
    not_elim_proof, not_intro_proof, or_claim, or_elim_proof, or_left_proof, or_right_proof, parse,
    parse_many, quote, returns_claim, returns_next_proof, returns_return_proof, rewrite_proof,
    step, step_equals_claim, step_proof, terminates_claim, true_claim, true_intro_proof,
    unfold_proof, use_proof, var, with,
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
