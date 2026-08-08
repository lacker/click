use super::*;
use crate::lang::click::diagnostics::*;
use crate::lang::click::proof::{
    instantiate_composite_resource_body_resources, pure_theorem_array_refs,
    pure_theorem_parameter_values,
};

mod declaration_expansion;
mod definition_validation;
mod expression_analysis;
mod type_validation;
pub(super) use declaration_expansion::*;
pub(super) use definition_validation::*;
pub(super) use expression_analysis::*;
pub(super) use type_validation::*;
