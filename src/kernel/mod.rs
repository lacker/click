pub mod calculus;
mod check;
mod eval;
mod theory;

pub use calculus::*;
pub use check::{
    alpha_eq_computation, alpha_eq_prop, check, check_in_context, free_symbols_prop,
    substitute_prop,
};
pub(crate) use check::{primitive_prop_holds, structural_primitive_prop_holds};
pub use eval::{computation_is_value, normal_form, normal_outcome, step};
pub use theory::{ComputationDefinitionError, Context, Theorem, TheoremError, Theory};

#[cfg(test)]
pub(crate) use check::check_in_bindings;
#[cfg(test)]
pub(crate) use theory::Bindings;

#[cfg(test)]
mod tests;
