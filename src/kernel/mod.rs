pub mod calculus;
mod check;
mod eval;
mod theory;

pub use calculus::*;
pub use check::{
    alpha_eq_prop, alpha_eq_term, check, check_in_context, free_symbols_prop, substitute_prop,
};
pub use eval::{normal_form, step, term_is_value};
pub use theory::{Context, Theorem, Theory};

#[cfg(test)]
pub(crate) use check::check_in_bindings;
#[cfg(test)]
pub(crate) use theory::Bindings;

#[cfg(test)]
mod tests;
