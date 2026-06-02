//! Standard definitions layered on top of the kernel.

pub mod list;
mod proof;
mod source;

use crate::{Computation, ComputationDefinitionError, Name, Symbol, Theorem, Theory};

pub use proof::{ProofElaborationError, SourceTheoremError};
pub use source::ParseError;

pub const TRUE: Symbol = Symbol(1);
pub const FALSE: Symbol = Symbol(2);

pub const REVERSE_ACC: Name = Name(1);
pub const REVERSE: Name = Name(2);
pub const REVERSE_ACC_COMPUTES_TO_LIST: Name = Name(3);
pub const REVERSE_COMPUTES_TO_LIST: Name = Name(4);
pub const REVERSE_NIL_COMPUTES_TO_LIST: Name = Name(6);
pub const APPEND: Name = Name(7);
pub const APPEND_NIL_COMPUTES_TO_LIST: Name = Name(8);
pub const APPEND_COMPUTES_TO_LIST: Name = Name(9);
pub const APPEND_NIL_RETURNS_RIGHT: Name = Name(10);
pub const APPEND_RIGHT_NIL: Name = Name(11);
pub const APPEND_CONS: Name = Name(12);
pub const APPEND_SINGLETON: Name = Name(13);
pub const APPEND_ASSOC: Name = Name(14);
pub const REVERSE_NIL: Name = Name(15);
pub const REVERSE_SINGLETON: Name = Name(16);
pub const REVERSE_ACC_APPEND: Name = Name(17);
pub const REVERSE_CONS: Name = Name(18);
pub const REVERSE_ACC_REVERSE: Name = Name(19);
pub const REVERSE_DOUBLE: Name = Name(20);
pub const REVERSE_ACC_OF_APPEND: Name = Name(21);
pub const REVERSE_APPEND: Name = Name(22);
pub const SNOC: Name = Name(23);
pub const SNOC_COMPUTES_TO_LIST: Name = Name(24);
pub const SNOC_NIL: Name = Name(25);
pub const SNOC_CONS: Name = Name(26);
pub const CONCAT: Name = Name(27);
pub const CONCAT_NIL: Name = Name(28);
pub const LAST: Name = Name(30);
pub const LAST_NIL_ERRORS: Name = Name(31);
pub const LAST_SINGLETON: Name = Name(32);
pub const LAST_CONS: Name = Name(33);
pub const INIT: Name = Name(34);
pub const INIT_NIL_ERRORS: Name = Name(35);
pub const INIT_SINGLETON: Name = Name(36);
pub const INIT_CONS: Name = Name(37);
pub const NULL: Name = Name(38);
pub const NULL_NIL: Name = Name(39);
pub const NULL_CONS: Name = Name(40);
pub const IS_SINGLETON: Name = Name(41);
pub const IS_SINGLETON_NIL: Name = Name(42);
pub const IS_SINGLETON_SINGLETON: Name = Name(43);
pub const IS_SINGLETON_CONS: Name = Name(44);

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

pub fn reverse_nil_exact() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_NIL)
}

pub fn reverse_singleton() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_SINGLETON)
}

pub fn reverse_acc_append() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_ACC_APPEND)
}

pub fn reverse_cons() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_CONS)
}

pub fn reverse_acc_reverse() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_ACC_REVERSE)
}

pub fn reverse_double() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_DOUBLE)
}

pub fn reverse_acc_of_append() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_ACC_OF_APPEND)
}

pub fn reverse_append() -> Option<Theorem> {
    list::checked_source_theorem(REVERSE_APPEND)
}

pub fn snoc_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(SNOC_COMPUTES_TO_LIST)
}

pub fn snoc_nil() -> Option<Theorem> {
    list::checked_source_theorem(SNOC_NIL)
}

pub fn snoc_cons() -> Option<Theorem> {
    list::checked_source_theorem(SNOC_CONS)
}

pub fn concat_nil() -> Option<Theorem> {
    list::checked_source_theorem(CONCAT_NIL)
}

pub fn last_nil_errors() -> Option<Theorem> {
    list::checked_source_theorem(LAST_NIL_ERRORS)
}

pub fn last_singleton() -> Option<Theorem> {
    list::checked_source_theorem(LAST_SINGLETON)
}

pub fn last_cons() -> Option<Theorem> {
    list::checked_source_theorem(LAST_CONS)
}

pub fn init_nil_errors() -> Option<Theorem> {
    list::checked_source_theorem(INIT_NIL_ERRORS)
}

pub fn init_singleton() -> Option<Theorem> {
    list::checked_source_theorem(INIT_SINGLETON)
}

pub fn init_cons() -> Option<Theorem> {
    list::checked_source_theorem(INIT_CONS)
}

pub fn null_nil() -> Option<Theorem> {
    list::checked_source_theorem(NULL_NIL)
}

pub fn null_cons() -> Option<Theorem> {
    list::checked_source_theorem(NULL_CONS)
}

pub fn is_singleton_nil() -> Option<Theorem> {
    list::checked_source_theorem(IS_SINGLETON_NIL)
}

pub fn is_singleton_singleton() -> Option<Theorem> {
    list::checked_source_theorem(IS_SINGLETON_SINGLETON)
}

pub fn is_singleton_cons() -> Option<Theorem> {
    list::checked_source_theorem(IS_SINGLETON_CONS)
}

pub fn append_nil_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_NIL_COMPUTES_TO_LIST)
}

pub fn append_computes_to_list() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_COMPUTES_TO_LIST)
}

pub fn append_nil_returns_right() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_NIL_RETURNS_RIGHT)
}

pub fn append_right_nil() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_RIGHT_NIL)
}

pub fn append_cons() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_CONS)
}

pub fn append_singleton() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_SINGLETON)
}

pub fn append_assoc() -> Option<Theorem> {
    list::checked_source_theorem(APPEND_ASSOC)
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

pub fn snoc() -> Computation {
    Computation::Ref(SNOC)
}

pub fn concat() -> Computation {
    Computation::Ref(CONCAT)
}

pub fn last() -> Computation {
    Computation::Ref(LAST)
}

pub fn init() -> Computation {
    Computation::Ref(INIT)
}

pub fn null() -> Computation {
    Computation::Ref(NULL)
}

pub fn is_singleton() -> Computation {
    Computation::Ref(IS_SINGLETON)
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
        assert_eq!(theory.computation(SNOC), Some(&list::snoc_definition()));
        assert_eq!(theory.computation(CONCAT), Some(&list::concat_definition()));
        assert_eq!(theory.computation(LAST), Some(&list::last_definition()));
        assert_eq!(theory.computation(INIT), Some(&list::init_definition()));
        assert_eq!(theory.computation(NULL), Some(&list::null_definition()));
        assert_eq!(
            theory.computation(IS_SINGLETON),
            Some(&list::is_singleton_definition())
        );
        assert_eq!(reverse_acc(), Computation::Ref(REVERSE_ACC));
        assert_eq!(reverse(), Computation::Ref(REVERSE));
        assert_eq!(append(), Computation::Ref(APPEND));
        assert_eq!(snoc(), Computation::Ref(SNOC));
        assert_eq!(concat(), Computation::Ref(CONCAT));
        assert_eq!(last(), Computation::Ref(LAST));
        assert_eq!(init(), Computation::Ref(INIT));
        assert_eq!(null(), Computation::Ref(NULL));
        assert_eq!(is_singleton(), Computation::Ref(IS_SINGLETON));
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
        assert_eq!(
            theory.reduce(&snoc()),
            Step::Reduced(list::snoc_definition())
        );
        assert_eq!(
            theory.reduce(&concat()),
            Step::Reduced(list::concat_definition())
        );
        assert_eq!(
            theory.reduce(&last()),
            Step::Reduced(list::last_definition())
        );
        assert_eq!(
            theory.reduce(&init()),
            Step::Reduced(list::init_definition())
        );
        assert_eq!(
            theory.reduce(&null()),
            Step::Reduced(list::null_definition())
        );
        assert_eq!(
            theory.reduce(&is_singleton()),
            Step::Reduced(list::is_singleton_definition())
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
        assert!(theory.theorem(APPEND_NIL_RETURNS_RIGHT).is_none());
        assert!(theory.theorem(APPEND_RIGHT_NIL).is_none());
        assert!(theory.theorem(APPEND_CONS).is_none());
        assert!(theory.theorem(APPEND_SINGLETON).is_none());
        assert!(theory.theorem(APPEND_ASSOC).is_none());
        assert!(theory.theorem(REVERSE_NIL).is_none());
        assert!(theory.theorem(REVERSE_SINGLETON).is_none());
        assert!(theory.theorem(REVERSE_ACC_APPEND).is_none());
        assert!(theory.theorem(REVERSE_CONS).is_none());
        assert!(theory.theorem(REVERSE_ACC_REVERSE).is_none());
        assert!(theory.theorem(REVERSE_DOUBLE).is_none());
        assert!(theory.theorem(REVERSE_ACC_OF_APPEND).is_none());
        assert!(theory.theorem(REVERSE_APPEND).is_none());
        assert!(theory.theorem(SNOC_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(SNOC_NIL).is_none());
        assert!(theory.theorem(SNOC_CONS).is_none());
        assert!(theory.theorem(CONCAT_NIL).is_none());
        assert!(theory.theorem(LAST_NIL_ERRORS).is_none());
        assert!(theory.theorem(LAST_SINGLETON).is_none());
        assert!(theory.theorem(LAST_CONS).is_none());
        assert!(theory.theorem(INIT_NIL_ERRORS).is_none());
        assert!(theory.theorem(INIT_SINGLETON).is_none());
        assert!(theory.theorem(INIT_CONS).is_none());
        assert!(theory.theorem(NULL_NIL).is_none());
        assert!(theory.theorem(NULL_CONS).is_none());
        assert!(theory.theorem(IS_SINGLETON_NIL).is_none());
        assert!(theory.theorem(IS_SINGLETON_SINGLETON).is_none());
        assert!(theory.theorem(IS_SINGLETON_CONS).is_none());
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
        assert!(theory.theorem(APPEND_NIL_RETURNS_RIGHT).is_none());
        assert!(theory.theorem(APPEND_RIGHT_NIL).is_none());
        assert!(theory.theorem(APPEND_CONS).is_none());
        assert!(theory.theorem(APPEND_SINGLETON).is_none());
        assert!(theory.theorem(APPEND_ASSOC).is_none());
        assert!(theory.theorem(REVERSE_NIL).is_none());
        assert!(theory.theorem(REVERSE_SINGLETON).is_none());
        assert!(theory.theorem(REVERSE_ACC_APPEND).is_none());
        assert!(theory.theorem(REVERSE_CONS).is_none());
        assert!(theory.theorem(REVERSE_ACC_REVERSE).is_none());
        assert!(theory.theorem(REVERSE_DOUBLE).is_none());
        assert!(theory.theorem(REVERSE_ACC_OF_APPEND).is_none());
        assert!(theory.theorem(REVERSE_APPEND).is_none());
        assert!(theory.theorem(SNOC_COMPUTES_TO_LIST).is_none());
        assert!(theory.theorem(SNOC_NIL).is_none());
        assert!(theory.theorem(SNOC_CONS).is_none());
        assert!(theory.theorem(CONCAT_NIL).is_none());
        assert!(theory.theorem(LAST_NIL_ERRORS).is_none());
        assert!(theory.theorem(LAST_SINGLETON).is_none());
        assert!(theory.theorem(LAST_CONS).is_none());
        assert!(theory.theorem(INIT_NIL_ERRORS).is_none());
        assert!(theory.theorem(INIT_SINGLETON).is_none());
        assert!(theory.theorem(INIT_CONS).is_none());
        assert!(theory.theorem(NULL_NIL).is_none());
        assert!(theory.theorem(NULL_CONS).is_none());
        assert!(theory.theorem(IS_SINGLETON_NIL).is_none());
        assert!(theory.theorem(IS_SINGLETON_SINGLETON).is_none());
        assert!(theory.theorem(IS_SINGLETON_CONS).is_none());
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
        let reverse_nil_exact_prop = list::reverse_nil_source_theorem();
        let reverse_singleton_prop = list::reverse_singleton_source_theorem();
        let reverse_acc_append_prop = list::reverse_acc_append_source_theorem();
        let reverse_cons_prop = list::reverse_cons_source_theorem();
        let reverse_acc_reverse_prop = list::reverse_acc_reverse_source_theorem();
        let reverse_double_prop = list::reverse_double_source_theorem();
        let reverse_acc_of_append_prop = list::reverse_acc_of_append_source_theorem();
        let reverse_append_prop = list::reverse_append_source_theorem();
        let snoc_prop = list::snoc_computes_to_list_source_theorem();
        let snoc_nil_prop = list::snoc_nil_source_theorem();
        let snoc_cons_prop = list::snoc_cons_source_theorem();
        let concat_nil_prop = list::concat_nil_source_theorem();
        let last_nil_errors_prop = list::last_nil_errors_source_theorem();
        let last_singleton_prop = list::last_singleton_source_theorem();
        let last_cons_prop = list::last_cons_source_theorem();
        let init_nil_errors_prop = list::init_nil_errors_source_theorem();
        let init_singleton_prop = list::init_singleton_source_theorem();
        let init_cons_prop = list::init_cons_source_theorem();
        let null_nil_prop = list::null_nil_source_theorem();
        let null_cons_prop = list::null_cons_source_theorem();
        let is_singleton_nil_prop = list::is_singleton_nil_source_theorem();
        let is_singleton_singleton_prop = list::is_singleton_singleton_source_theorem();
        let is_singleton_cons_prop = list::is_singleton_cons_source_theorem();
        let append_nil_prop = list::append_nil_computes_to_list_source_theorem();
        let append_prop = list::append_computes_to_list_source_theorem();
        let append_nil_returns_right_prop = list::append_nil_returns_right_source_theorem();
        let append_right_nil_prop = list::append_right_nil_source_theorem();
        let append_cons_prop = list::append_cons_source_theorem();
        let append_singleton_prop = list::append_singleton_source_theorem();
        let append_assoc_prop = list::append_assoc_source_theorem();

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
        assert_eq!(theory.theorem(REVERSE_NIL), Some(&reverse_nil_exact_prop));
        assert_eq!(
            theory.theorem(REVERSE_SINGLETON),
            Some(&reverse_singleton_prop)
        );
        assert_eq!(
            theory.theorem(REVERSE_ACC_APPEND),
            Some(&reverse_acc_append_prop)
        );
        assert_eq!(theory.theorem(REVERSE_CONS), Some(&reverse_cons_prop));
        assert_eq!(
            theory.theorem(REVERSE_ACC_REVERSE),
            Some(&reverse_acc_reverse_prop)
        );
        assert_eq!(theory.theorem(REVERSE_DOUBLE), Some(&reverse_double_prop));
        assert_eq!(
            theory.theorem(REVERSE_ACC_OF_APPEND),
            Some(&reverse_acc_of_append_prop)
        );
        assert_eq!(theory.theorem(REVERSE_APPEND), Some(&reverse_append_prop));
        assert_eq!(theory.theorem(SNOC_COMPUTES_TO_LIST), Some(&snoc_prop));
        assert_eq!(theory.theorem(SNOC_NIL), Some(&snoc_nil_prop));
        assert_eq!(theory.theorem(SNOC_CONS), Some(&snoc_cons_prop));
        assert_eq!(theory.theorem(CONCAT_NIL), Some(&concat_nil_prop));
        assert_eq!(theory.theorem(LAST_NIL_ERRORS), Some(&last_nil_errors_prop));
        assert_eq!(theory.theorem(LAST_SINGLETON), Some(&last_singleton_prop));
        assert_eq!(theory.theorem(LAST_CONS), Some(&last_cons_prop));
        assert_eq!(theory.theorem(INIT_NIL_ERRORS), Some(&init_nil_errors_prop));
        assert_eq!(theory.theorem(INIT_SINGLETON), Some(&init_singleton_prop));
        assert_eq!(theory.theorem(INIT_CONS), Some(&init_cons_prop));
        assert_eq!(theory.theorem(NULL_NIL), Some(&null_nil_prop));
        assert_eq!(theory.theorem(NULL_CONS), Some(&null_cons_prop));
        assert_eq!(
            theory.theorem(IS_SINGLETON_NIL),
            Some(&is_singleton_nil_prop)
        );
        assert_eq!(
            theory.theorem(IS_SINGLETON_SINGLETON),
            Some(&is_singleton_singleton_prop)
        );
        assert_eq!(
            theory.theorem(IS_SINGLETON_CONS),
            Some(&is_singleton_cons_prop)
        );
        assert_eq!(
            theory.theorem(APPEND_NIL_COMPUTES_TO_LIST),
            Some(&append_nil_prop)
        );
        assert_eq!(theory.theorem(APPEND_COMPUTES_TO_LIST), Some(&append_prop));
        assert_eq!(
            theory.theorem(APPEND_NIL_RETURNS_RIGHT),
            Some(&append_nil_returns_right_prop)
        );
        assert_eq!(
            theory.theorem(APPEND_RIGHT_NIL),
            Some(&append_right_nil_prop)
        );
        assert_eq!(theory.theorem(APPEND_CONS), Some(&append_cons_prop));
        assert_eq!(
            theory.theorem(APPEND_SINGLETON),
            Some(&append_singleton_prop)
        );
        assert_eq!(theory.theorem(APPEND_ASSOC), Some(&append_assoc_prop));
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
            reverse_nil_exact()
                .expect("reverse nil exact theorem source proof should check with dependencies")
                .prop(),
            &reverse_nil_exact_prop,
        );
        assert_eq!(
            reverse_singleton()
                .expect("reverse singleton theorem source proof should check with dependencies")
                .prop(),
            &reverse_singleton_prop,
        );
        assert_eq!(
            reverse_acc_append()
                .expect("reverse accumulator theorem source proof should check with dependencies")
                .prop(),
            &reverse_acc_append_prop,
        );
        assert_eq!(
            reverse_cons()
                .expect("reverse cons theorem source proof should check with dependencies")
                .prop(),
            &reverse_cons_prop,
        );
        assert_eq!(
            reverse_acc_reverse()
                .expect("reverse accumulator inverse theorem source proof should check with dependencies")
                .prop(),
            &reverse_acc_reverse_prop,
        );
        assert_eq!(
            reverse_double()
                .expect("reverse double theorem source proof should check with dependencies")
                .prop(),
            &reverse_double_prop,
        );
        assert_eq!(
            reverse_acc_of_append()
                .expect(
                    "reverse accumulator append theorem source proof should check with dependencies"
                )
                .prop(),
            &reverse_acc_of_append_prop,
        );
        assert_eq!(
            reverse_append()
                .expect("reverse append theorem source proof should check with dependencies")
                .prop(),
            &reverse_append_prop,
        );
        assert_eq!(
            snoc_computes_to_list()
                .expect("snoc theorem source proof should check with dependencies")
                .prop(),
            &snoc_prop,
        );
        assert_eq!(
            snoc_nil()
                .expect("snoc nil theorem source proof should check with dependencies")
                .prop(),
            &snoc_nil_prop,
        );
        assert_eq!(
            snoc_cons()
                .expect("snoc cons theorem source proof should check with dependencies")
                .prop(),
            &snoc_cons_prop,
        );
        assert_eq!(
            concat_nil()
                .expect("concat nil theorem source proof should check with dependencies")
                .prop(),
            &concat_nil_prop,
        );
        assert_eq!(
            last_nil_errors()
                .expect("last nil theorem source proof should check with dependencies")
                .prop(),
            &last_nil_errors_prop,
        );
        assert_eq!(
            last_singleton()
                .expect("last singleton theorem source proof should check with dependencies")
                .prop(),
            &last_singleton_prop,
        );
        assert_eq!(
            last_cons()
                .expect("last cons theorem source proof should check with dependencies")
                .prop(),
            &last_cons_prop,
        );
        assert_eq!(
            init_nil_errors()
                .expect("init nil theorem source proof should check with dependencies")
                .prop(),
            &init_nil_errors_prop,
        );
        assert_eq!(
            init_singleton()
                .expect("init singleton theorem source proof should check with dependencies")
                .prop(),
            &init_singleton_prop,
        );
        assert_eq!(
            init_cons()
                .expect("init cons theorem source proof should check with dependencies")
                .prop(),
            &init_cons_prop,
        );
        assert_eq!(
            null_nil()
                .expect("null nil theorem source proof should check with dependencies")
                .prop(),
            &null_nil_prop,
        );
        assert_eq!(
            null_cons()
                .expect("null cons theorem source proof should check with dependencies")
                .prop(),
            &null_cons_prop,
        );
        assert_eq!(
            is_singleton_nil()
                .expect("is-singleton nil theorem source proof should check with dependencies")
                .prop(),
            &is_singleton_nil_prop,
        );
        assert_eq!(
            is_singleton_singleton()
                .expect(
                    "is-singleton singleton theorem source proof should check with dependencies"
                )
                .prop(),
            &is_singleton_singleton_prop,
        );
        assert_eq!(
            is_singleton_cons()
                .expect("is-singleton cons theorem source proof should check with dependencies")
                .prop(),
            &is_singleton_cons_prop,
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
        assert_eq!(
            append_nil_returns_right()
                .expect("append nil exact theorem source proof should check with dependencies")
                .prop(),
            &append_nil_returns_right_prop,
        );
        assert_eq!(
            append_right_nil()
                .expect("append right nil theorem source proof should check with dependencies")
                .prop(),
            &append_right_nil_prop,
        );
        assert_eq!(
            append_cons()
                .expect("append cons theorem source proof should check with dependencies")
                .prop(),
            &append_cons_prop,
        );
        assert_eq!(
            append_singleton()
                .expect("append singleton theorem source proof should check with dependencies")
                .prop(),
            &append_singleton_prop,
        );
        assert_eq!(
            append_assoc()
                .expect("append associativity theorem source proof should check with dependencies")
                .prop(),
            &append_assoc_prop,
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
