//! Standard definitions layered on top of the kernel.

pub mod list;
mod proof;
mod source;

use crate::{Computation, ComputationDefinitionError, Name, Theorem, Theory};

pub use proof::{ProofElaborationError, SourceTheoremError};
pub use source::ParseError;

pub const REVERSE_ACC: Name = Name(1);
pub const REVERSE: Name = Name(2);
pub const REVERSE_ACC_COMPUTES_TO_LIST: Name = Name(3);
pub const REVERSE_COMPUTES_TO_LIST: Name = Name(4);
pub const REVERSE_NIL_COMPUTES_TO_LIST: Name = Name(6);
pub const APPEND: Name = Name(7);
pub const APPEND_NIL_COMPUTES_TO_LIST: Name = Name(8);
pub const APPEND_COMPUTES_TO_LIST: Name = Name(9);

const MODULES: &[source::ModuleSpec] = &[list::MODULE];

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceComputationError {
    ModuleParseFailed(ParseError),
    ComputationRejected {
        computation: Name,
        error: ComputationDefinitionError,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceLoadError {
    ModuleParseFailed(ParseError),
    Computation(SourceComputationError),
    Theorem(SourceTheoremError),
}

pub fn theory() -> Theory {
    try_theory().expect("prelude source should define a valid theory")
}

pub fn try_theory() -> Result<Theory, SourceLoadError> {
    let mut theory = Theory::new();
    try_define_in_theory(&mut theory)?;
    Ok(theory)
}

pub fn computation_theory() -> Theory {
    try_computation_theory().expect("prelude source should define valid computations")
}

pub fn try_computation_theory() -> Result<Theory, SourceComputationError> {
    let mut theory = Theory::new();
    try_define_computations_in_theory(&mut theory)?;
    Ok(theory)
}

pub fn define_in_theory(theory: &mut Theory) -> bool {
    try_define_in_theory(theory).is_ok()
}

pub fn try_define_in_theory(theory: &mut Theory) -> Result<(), SourceLoadError> {
    let modules = parse_modules().map_err(SourceLoadError::ModuleParseFailed)?;

    define_modules_in_theory_result(theory, &modules)
}

fn parse_modules() -> Result<Vec<source::ParsedModule>, ParseError> {
    MODULES.iter().map(source::ModuleSpec::parse).collect()
}

fn define_modules_in_theory_result(
    theory: &mut Theory,
    modules: &[source::ParsedModule],
) -> Result<(), SourceLoadError> {
    for module in modules {
        define_module_computations_result(theory, module).map_err(SourceLoadError::Computation)?;
    }

    for module in modules {
        define_module_theorems_result(theory, module).map_err(SourceLoadError::Theorem)?;
    }

    Ok(())
}

#[cfg(test)]
fn define_module_in_theory_result(
    theory: &mut Theory,
    module: &source::ParsedModule,
) -> Result<(), SourceLoadError> {
    define_modules_in_theory_result(theory, std::slice::from_ref(module))
}

pub fn define_computations_in_theory(theory: &mut Theory) -> bool {
    try_define_computations_in_theory(theory).is_ok()
}

pub fn try_define_computations_in_theory(
    theory: &mut Theory,
) -> Result<(), SourceComputationError> {
    let modules = parse_modules().map_err(SourceComputationError::ModuleParseFailed)?;

    for module in &modules {
        define_module_computations_result(theory, module)?;
    }

    Ok(())
}

fn define_module_computations_result(
    theory: &mut Theory,
    module: &source::ParsedModule,
) -> Result<(), SourceComputationError> {
    for (name, computation) in &module.computations {
        theory
            .define_computation_result(*name, computation)
            .map_err(|error| SourceComputationError::ComputationRejected {
                computation: *name,
                error,
            })?;
    }

    Ok(())
}

pub fn define_theorems_in_theory(theory: &mut Theory) -> bool {
    try_define_theorems_in_theory(theory).is_ok()
}

pub fn try_define_theorems_in_theory(theory: &mut Theory) -> Result<(), SourceTheoremError> {
    let modules = parse_modules().map_err(SourceTheoremError::ModuleParseFailed)?;

    for module in &modules {
        define_module_theorems_result(theory, module)?;
    }

    Ok(())
}

fn define_module_theorems_result(
    theory: &mut Theory,
    module: &source::ParsedModule,
) -> Result<(), SourceTheoremError> {
    for theorem in &module.theorems {
        proof::define_source_theorem(theorem, theory)?;
    }

    Ok(())
}

pub fn reverse_acc_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_ACC_COMPUTES_TO_LIST)
}

pub fn reverse_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_COMPUTES_TO_LIST)
}

pub fn reverse_nil_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_NIL_COMPUTES_TO_LIST)
}

pub fn append_nil_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_NIL_COMPUTES_TO_LIST)
}

pub fn append_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_COMPUTES_TO_LIST)
}

pub fn reverse_acc() -> Computation {
    Computation::Ref(REVERSE_ACC)
}

pub fn reverse() -> Computation {
    Computation::Ref(REVERSE)
}

pub fn append() -> Computation {
    Computation::Ref(APPEND)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ComputationDefinitionError, Step, TheoremError, computes_to_list};

    #[test]
    fn theory_defines_reverse() {
        let theory = theory();
        let try_theory = try_theory().expect("prelude should load");

        assert_eq!(
            theory.computation(REVERSE_ACC),
            Some(&list::reverse_acc_definition())
        );
        assert_eq!(
            try_theory.computation(REVERSE_ACC),
            Some(&list::reverse_acc_definition())
        );
        assert_eq!(
            theory.computation(REVERSE),
            Some(&list::reverse_definition())
        );
        assert_eq!(theory.computation(APPEND), Some(&list::append_definition()));
        assert_eq!(reverse_acc(), Computation::Ref(REVERSE_ACC));
        assert_eq!(reverse(), Computation::Ref(REVERSE));
        assert_eq!(append(), Computation::Ref(APPEND));
        assert_eq!(
            theory.reduce(&reverse_acc()),
            Step::Reduced(list::reverse_acc_definition())
        );
        assert_eq!(
            theory.reduce(&reverse()),
            Step::Reduced(list::reverse_definition())
        );
        assert_eq!(
            theory.reduce(&append()),
            Step::Reduced(list::append_definition())
        );
    }

    #[test]
    fn computation_theory_does_not_define_theorems() {
        let theory = computation_theory();
        let try_theory = try_computation_theory().expect("prelude computations should load");

        assert!(theory.theorem(REVERSE_ACC_COMPUTES_TO_LIST).is_none());
        assert!(try_theory.theorem(REVERSE_ACC_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(REVERSE_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(REVERSE_NIL_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(APPEND_NIL_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(APPEND_COMPUTES_TO_LIST).is_none());
    }

    #[test]
    fn computation_definition_diagnostics_report_kernel_rejection() {
        let mut theory = Theory::new();

        assert!(theory.define_computation(REVERSE_ACC, &Computation::Nil));
        assert!(!define_computations_in_theory(&mut theory));
        assert_eq!(
            try_define_computations_in_theory(&mut theory),
            Err(SourceComputationError::ComputationRejected {
                computation: REVERSE_ACC,
                error: ComputationDefinitionError::ComputationNameAlreadyDefined(REVERSE_ACC),
            })
        );
    }

    #[test]
    fn full_source_load_diagnostics_report_computation_failures() {
        let mut theory = Theory::new();

        assert!(theory.define_computation(REVERSE_ACC, &Computation::Nil));
        assert!(!define_in_theory(&mut theory));
        assert_eq!(
            try_define_in_theory(&mut theory),
            Err(SourceLoadError::Computation(
                SourceComputationError::ComputationRejected {
                    computation: REVERSE_ACC,
                    error: ComputationDefinitionError::ComputationNameAlreadyDefined(REVERSE_ACC),
                }
            ))
        );
    }

    #[test]
    fn theorem_definitions_require_computations() {
        let mut theory = Theory::new();

        assert!(!define_theorems_in_theory(&mut theory));
        let Err(SourceTheoremError::ProofElaborationFailed { theorem, error }) =
            try_define_theorems_in_theory(&mut theory)
        else {
            panic!("theorem loading should report proof elaboration failure");
        };
        assert_eq!(theorem, REVERSE_ACC_COMPUTES_TO_LIST);
        assert!(proof_error_contains_evaluation_failure(&error));
        assert!(theory.theorem(REVERSE_ACC_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(REVERSE_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(REVERSE_NIL_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(APPEND_NIL_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(APPEND_COMPUTES_TO_LIST).is_none());
    }

    #[test]
    fn full_source_load_diagnostics_report_theorem_failures() {
        let module = source::parse_module(
            "
            (theorem bad
              (equal nil (quote unit))
              (proof (eval-to nil nil)))
            ",
            &[],
            &[source::NameBinding {
                spelling: "bad",
                name: Name(99),
            }],
            &[source::SymbolBinding {
                spelling: "unit",
                symbol: list::UNIT,
            }],
        )
        .expect("synthetic module should parse");
        let mut theory = Theory::new();

        assert_eq!(
            define_module_in_theory_result(&mut theory, &module),
            Err(SourceLoadError::Theorem(
                SourceTheoremError::TheoremRejected {
                    theorem: Name(99),
                    error: TheoremError::InvalidProof,
                }
            ))
        );
    }

    fn proof_error_contains_evaluation_failure(error: &ProofElaborationError) -> bool {
        match error {
            ProofElaborationError::EvaluationFailed(_) => true,
            ProofElaborationError::InSubproof { error, .. } => {
                proof_error_contains_evaluation_failure(error)
            }
            ProofElaborationError::UnknownTheorem(_) => false,
        }
    }

    #[test]
    fn source_theorem_diagnostics_report_kernel_rejection() {
        let module = source::parse_module(
            "
            (theorem bad
              (equal nil (quote unit))
              (proof (eval-to nil nil)))
            ",
            &[],
            &[source::NameBinding {
                spelling: "bad",
                name: Name(99),
            }],
            &[source::SymbolBinding {
                spelling: "unit",
                symbol: list::UNIT,
            }],
        )
        .expect("synthetic module should parse");

        assert_eq!(
            proof::source_theorem_result(module, Name(99), Theory::new()),
            Err(SourceTheoremError::TheoremRejected {
                theorem: Name(99),
                error: TheoremError::InvalidProof,
            })
        );
    }

    #[test]
    fn source_theorem_diagnostics_report_unknown_known_theorem() {
        let module = source::parse_module(
            "
            (theorem bad
              (equal nil nil)
              (proof (known later)))
            (theorem later
              (equal nil nil)
              (proof (eval-to nil nil)))
            ",
            &[],
            &[
                source::NameBinding {
                    spelling: "bad",
                    name: Name(99),
                },
                source::NameBinding {
                    spelling: "later",
                    name: Name(100),
                },
            ],
            &[],
        )
        .expect("synthetic module should parse");

        assert_eq!(
            proof::source_theorem_result(module, Name(99), Theory::new()),
            Err(SourceTheoremError::ProofElaborationFailed {
                theorem: Name(99),
                error: ProofElaborationError::UnknownTheorem(Name(100)),
            })
        );
    }

    #[test]
    fn theory_defines_reverse_theorems() {
        let theory = theory();
        let reverse_acc_prop = list::reverse_acc_computes_to_list_source_theorem();
        let reverse_prop = list::reverse_computes_to_list_source_theorem();
        let reverse_nil_prop = list::reverse_nil_computes_to_list_source_theorem();
        let append_nil_prop = list::append_nil_computes_to_list_source_theorem();
        let append_prop = list::append_computes_to_list_source_theorem();

        assert_eq!(
            theory.theorem(REVERSE_ACC_COMPUTES_TO_LIST),
            Some(&reverse_acc_prop)
        );
        assert_eq!(
            theory.theorem(REVERSE_COMPUTES_TO_LIST),
            Some(&reverse_prop)
        );
        assert_eq!(
            theory.theorem(REVERSE_NIL_COMPUTES_TO_LIST),
            Some(&reverse_nil_prop)
        );
        assert_eq!(
            theory.theorem(APPEND_NIL_COMPUTES_TO_LIST),
            Some(&append_nil_prop)
        );
        assert_eq!(theory.theorem(APPEND_COMPUTES_TO_LIST), Some(&append_prop));
        assert_eq!(
            theory
                .known(REVERSE_COMPUTES_TO_LIST)
                .expect("reverse theorem should be defined")
                .prop(),
            &reverse_prop,
        );
        assert_eq!(
            reverse_computes_to_list()
                .expect("reverse theorem source proof should check with dependencies")
                .prop(),
            &reverse_prop,
        );
        assert_eq!(
            reverse_nil_computes_to_list()
                .expect("reverse nil theorem source proof should check with dependencies")
                .prop(),
            &reverse_nil_prop,
        );
        assert_eq!(
            append_nil_computes_to_list()
                .expect("append nil theorem source proof should check with dependencies")
                .prop(),
            &append_nil_prop,
        );
        assert_eq!(
            append_computes_to_list()
                .expect("append theorem source proof should check with dependencies")
                .prop(),
            &append_prop,
        );
    }

    #[test]
    fn prelude_theory_instantiates_named_reverse_theorem() {
        let theory = theory();
        let reverse = theory
            .known(REVERSE_COMPUTES_TO_LIST)
            .expect("reverse theorem should be defined");
        let instantiated = theory
            .forall_elim(&reverse, list::nil())
            .expect("known theorem should instantiate in its theory");

        assert_eq!(
            instantiated.prop(),
            &computes_to_list(
                list::reverse_computes_to_list_source_result_symbol(),
                list::reverse_call(list::nil()),
            )
        );
    }
}
