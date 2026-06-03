//! Standard definitions layered on top of the kernel.

pub mod list;

use std::sync::OnceLock;

use crate::{
    Computation, Name, Symbol, Theorem, Theory,
    elab::{
        ElabEnv, LoadedSource,
        loader::{define_module_computations_result, define_module_theorems_result},
        source,
    },
};

pub use crate::elab::{
    ParseError, ProofElaborationError, SourceComputationError, SourceFileLoadError,
    SourceLoadError, SourceTheoremError,
};

const SOURCES: &[&str] = &[list::SOURCE];
static LOADED_PRELUDE: OnceLock<Result<LoadedSource, SourceLoadError>> = OnceLock::new();
static LOADED_PRELUDE_COMPUTATIONS: OnceLock<Result<LoadedSource, SourceComputationError>> =
    OnceLock::new();

pub type LoadedPrelude = LoadedSource;

pub fn loaded() -> LoadedPrelude {
    try_loaded().expect("prelude source should define a valid theory")
}

pub fn try_loaded() -> Result<LoadedPrelude, SourceLoadError> {
    loaded_source().cloned()
}

pub fn loaded_computations() -> LoadedPrelude {
    try_loaded_computations().expect("prelude source should define valid computations")
}

pub fn try_loaded_computations() -> Result<LoadedPrelude, SourceComputationError> {
    loaded_computation_source().cloned()
}

pub fn computation_name(spelling: &str) -> Option<Name> {
    loaded_computation_source().ok()?.computation(spelling)
}

pub fn theorem_name(spelling: &str) -> Option<Name> {
    loaded_computation_source().ok()?.theorem(spelling)
}

pub fn symbol_name(spelling: &str) -> Option<Symbol> {
    loaded_computation_source().ok()?.symbol(spelling)
}

fn expect_computation_name(spelling: &str) -> Name {
    computation_name(spelling).expect("prelude source should define requested computation")
}

fn checked_source_theorem(spelling: &str) -> Option<Theorem> {
    list::checked_source_theorem(theorem_name(spelling)?)
}

pub fn theory() -> Theory {
    loaded().into_theory()
}

pub fn try_theory() -> Result<Theory, SourceLoadError> {
    try_loaded().map(LoadedPrelude::into_theory)
}

pub fn computation_theory() -> Theory {
    loaded_computations().into_theory()
}

pub fn try_computation_theory() -> Result<Theory, SourceComputationError> {
    try_loaded_computations().map(LoadedPrelude::into_theory)
}

pub fn define_in_theory(theory: &mut Theory) -> bool {
    try_define_in_theory(theory).is_ok()
}

pub fn try_define_in_theory(theory: &mut Theory) -> Result<(), SourceLoadError> {
    let loaded = loaded_source()?;

    define_modules_in_theory_result(theory, loaded.modules())
}

fn loaded_source() -> Result<&'static LoadedSource, SourceLoadError> {
    LOADED_PRELUDE
        .get_or_init(load_prelude_source)
        .as_ref()
        .map_err(|error| error.clone())
}

fn loaded_computation_source() -> Result<&'static LoadedSource, SourceComputationError> {
    LOADED_PRELUDE_COMPUTATIONS
        .get_or_init(load_prelude_computation_source)
        .as_ref()
        .map_err(|error| error.clone())
}

pub(crate) fn parsed_prelude_env() -> Result<&'static ElabEnv, SourceComputationError> {
    loaded_computation_source().map(LoadedSource::env)
}

pub(crate) fn parsed_list_module() -> Result<&'static source::ParsedModule, SourceComputationError>
{
    loaded_computation_source().map(|loaded| {
        loaded
            .module(0)
            .expect("prelude should contain the list module")
    })
}

fn load_prelude_source() -> Result<LoadedSource, SourceLoadError> {
    let mut loaded = LoadedSource::with_env(prelude_env());

    for source in SOURCES {
        loaded.load_str(source)?;
    }

    Ok(loaded)
}

fn load_prelude_computation_source() -> Result<LoadedSource, SourceComputationError> {
    let mut loaded = LoadedSource::with_env(prelude_env());

    for source in SOURCES {
        loaded.load_computations_str(source)?;
    }

    Ok(loaded)
}

pub(crate) fn prelude_env() -> ElabEnv {
    let mut env = ElabEnv::new();

    env.intern_symbol(":true");
    env.intern_symbol(":false");
    env.intern_symbol("unit");

    env
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
    let loaded = loaded_computation_source()?;

    for module in loaded.modules() {
        define_module_computations_result(theory, module)?;
    }

    Ok(())
}

pub fn define_theorems_in_theory(theory: &mut Theory) -> bool {
    try_define_theorems_in_theory(theory).is_ok()
}

pub fn try_define_theorems_in_theory(theory: &mut Theory) -> Result<(), SourceTheoremError> {
    let loaded = loaded_computation_source().map_err(|error| match error {
        SourceComputationError::ModuleParseFailed(error) => {
            SourceTheoremError::ModuleParseFailed(error)
        }
        SourceComputationError::ComputationRejected { .. } => {
            unreachable!("fresh prelude computation loading should not reject definitions")
        }
    })?;

    for module in loaded.modules() {
        define_module_theorems_result(theory, module)?;
    }

    Ok(())
}

pub fn reverse_acc_computes_to_list() -> Option<Theorem> {
    checked_source_theorem("reverse_acc_computes_to_list")
}

pub fn reverse_computes_to_list() -> Option<Theorem> {
    checked_source_theorem("reverse_computes_to_list")
}

pub fn reverse_nil_computes_to_list() -> Option<Theorem> {
    checked_source_theorem("reverse_nil_computes_to_list")
}

pub fn reverse_nil_exact() -> Option<Theorem> {
    checked_source_theorem("reverse_nil")
}

pub fn reverse_singleton() -> Option<Theorem> {
    checked_source_theorem("reverse_singleton")
}

pub fn reverse_acc_append() -> Option<Theorem> {
    checked_source_theorem("reverse_acc_append")
}

pub fn reverse_cons() -> Option<Theorem> {
    checked_source_theorem("reverse_cons")
}

pub fn reverse_acc_reverse() -> Option<Theorem> {
    checked_source_theorem("reverse_acc_reverse")
}

pub fn reverse_double() -> Option<Theorem> {
    checked_source_theorem("reverse_double")
}

pub fn reverse_acc_of_append() -> Option<Theorem> {
    checked_source_theorem("reverse_acc_of_append")
}

pub fn reverse_append() -> Option<Theorem> {
    checked_source_theorem("reverse_append")
}

pub fn snoc_computes_to_list() -> Option<Theorem> {
    checked_source_theorem("snoc_computes_to_list")
}

pub fn snoc_nil() -> Option<Theorem> {
    checked_source_theorem("snoc_nil")
}

pub fn snoc_cons() -> Option<Theorem> {
    checked_source_theorem("snoc_cons")
}

pub fn concat_nil() -> Option<Theorem> {
    checked_source_theorem("concat_nil")
}

pub fn last_nil_errors() -> Option<Theorem> {
    checked_source_theorem("last_nil_errors")
}

pub fn last_singleton() -> Option<Theorem> {
    checked_source_theorem("last_singleton")
}

pub fn last_cons() -> Option<Theorem> {
    checked_source_theorem("last_cons")
}

pub fn init_nil_errors() -> Option<Theorem> {
    checked_source_theorem("init_nil_errors")
}

pub fn init_singleton() -> Option<Theorem> {
    checked_source_theorem("init_singleton")
}

pub fn init_cons() -> Option<Theorem> {
    checked_source_theorem("init_cons")
}

pub fn null_nil() -> Option<Theorem> {
    checked_source_theorem("null_nil")
}

pub fn null_cons() -> Option<Theorem> {
    checked_source_theorem("null_cons")
}

pub fn is_singleton_nil() -> Option<Theorem> {
    checked_source_theorem("is_singleton_nil")
}

pub fn is_singleton_singleton() -> Option<Theorem> {
    checked_source_theorem("is_singleton_singleton")
}

pub fn is_singleton_cons() -> Option<Theorem> {
    checked_source_theorem("is_singleton_cons")
}

pub fn append_nil_computes_to_list() -> Option<Theorem> {
    checked_source_theorem("append_nil_computes_to_list")
}

pub fn append_computes_to_list() -> Option<Theorem> {
    checked_source_theorem("append_computes_to_list")
}

pub fn append_nil_returns_right() -> Option<Theorem> {
    checked_source_theorem("append_nil_returns_right")
}

pub fn append_right_nil() -> Option<Theorem> {
    checked_source_theorem("append_right_nil")
}

pub fn append_cons() -> Option<Theorem> {
    checked_source_theorem("append_cons")
}

pub fn append_singleton() -> Option<Theorem> {
    checked_source_theorem("append_singleton")
}

pub fn append_assoc() -> Option<Theorem> {
    checked_source_theorem("append_assoc")
}

pub fn reverse_acc() -> Computation {
    Computation::Ref(expect_computation_name("reverse_acc"))
}

pub fn reverse() -> Computation {
    Computation::Ref(expect_computation_name("reverse"))
}

pub fn append() -> Computation {
    Computation::Ref(expect_computation_name("append"))
}

pub fn snoc() -> Computation {
    Computation::Ref(expect_computation_name("snoc"))
}

pub fn concat() -> Computation {
    Computation::Ref(expect_computation_name("concat"))
}

pub fn last() -> Computation {
    Computation::Ref(expect_computation_name("last"))
}

pub fn init() -> Computation {
    Computation::Ref(expect_computation_name("init"))
}

pub fn null() -> Computation {
    Computation::Ref(expect_computation_name("null"))
}

pub fn is_singleton() -> Computation {
    Computation::Ref(expect_computation_name("is-singleton"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ComputationDefinitionError, Step, TheoremError, computes_to_list, elab::proof};

    fn computation(spelling: &str) -> Name {
        computation_name(spelling).expect("prelude should define requested computation")
    }

    fn theorem(spelling: &str) -> Name {
        theorem_name(spelling).expect("prelude should define requested theorem")
    }

    fn symbol(spelling: &str) -> Symbol {
        symbol_name(spelling).expect("prelude should define requested symbol")
    }

    fn parse_test_module(source: &str) -> (source::ParsedModule, ElabEnv) {
        let mut env = prelude_env();
        let module = env
            .parse_module(source)
            .expect("synthetic module should parse");
        (module, env)
    }

    fn prelude_theorem_names() -> Vec<Name> {
        [
            "reverse_acc_computes_to_list",
            "reverse_computes_to_list",
            "reverse_nil_computes_to_list",
            "reverse_nil",
            "reverse_singleton",
            "append_nil_computes_to_list",
            "append_computes_to_list",
            "append_nil_returns_right",
            "append_right_nil",
            "append_cons",
            "append_singleton",
            "append_assoc",
            "reverse_acc_append",
            "reverse_cons",
            "reverse_acc_reverse",
            "reverse_double",
            "reverse_acc_of_append",
            "reverse_append",
            "snoc_computes_to_list",
            "snoc_nil",
            "snoc_cons",
            "concat_nil",
            "last_nil_errors",
            "last_singleton",
            "last_cons",
            "init_nil_errors",
            "init_singleton",
            "init_cons",
            "null_nil",
            "null_cons",
            "is_singleton_nil",
            "is_singleton_singleton",
            "is_singleton_cons",
        ]
        .into_iter()
        .map(theorem)
        .collect()
    }

    #[test]
    fn loaded_prelude_exposes_theory_and_source_environment() {
        let loaded = loaded();

        assert_eq!(loaded.computation("append"), Some(computation("append")));
        assert_eq!(
            loaded.theorem("append_assoc"),
            Some(theorem("append_assoc"))
        );
        assert_eq!(loaded.symbol(":true"), Some(symbol(":true")));
        assert_eq!(loaded.symbol(":false"), Some(symbol(":false")));
        assert_eq!(loaded.computation("missing"), None);
        assert_eq!(loaded.theorem("missing"), None);
        assert_eq!(loaded.symbol("missing"), None);
        assert_eq!(
            loaded.theory().computation(computation("append")),
            Some(&list::append_definition())
        );
        assert_eq!(
            loaded.theory().theorem(theorem("append_assoc")),
            Some(&list::append_assoc_source_theorem())
        );
        assert_eq!(
            loaded.env().computation("reverse_acc"),
            Some(computation("reverse_acc"))
        );

        assert_eq!(
            computation_name("is-singleton"),
            Some(computation("is-singleton"))
        );
        assert_eq!(
            theorem_name("reverse_double"),
            Some(theorem("reverse_double"))
        );
        assert_eq!(symbol_name(":true"), Some(symbol(":true")));
    }

    #[test]
    fn loaded_computation_prelude_keeps_env_without_defining_theorems() {
        let loaded = loaded_computations();

        assert_eq!(loaded.computation("reverse"), Some(computation("reverse")));
        assert_eq!(
            loaded.theorem("append_assoc"),
            Some(theorem("append_assoc"))
        );
        assert_eq!(
            loaded.theory().computation(computation("reverse")),
            Some(&list::reverse_definition())
        );
        assert!(loaded.theory().theorem(theorem("append_assoc")).is_none());
    }

    #[test]
    fn theory_defines_reverse() {
        let theory = theory();
        let try_theory = try_theory().expect("prelude should load");

        assert_eq!(
            theory.computation(computation("reverse_acc")),
            Some(&list::reverse_acc_definition())
        );
        assert_eq!(
            try_theory.computation(computation("reverse_acc")),
            Some(&list::reverse_acc_definition())
        );
        assert_eq!(
            theory.computation(computation("reverse")),
            Some(&list::reverse_definition())
        );
        assert_eq!(
            theory.computation(computation("append")),
            Some(&list::append_definition())
        );
        assert_eq!(
            theory.computation(computation("snoc")),
            Some(&list::snoc_definition())
        );
        assert_eq!(
            theory.computation(computation("concat")),
            Some(&list::concat_definition())
        );
        assert_eq!(
            theory.computation(computation("last")),
            Some(&list::last_definition())
        );
        assert_eq!(
            theory.computation(computation("init")),
            Some(&list::init_definition())
        );
        assert_eq!(
            theory.computation(computation("null")),
            Some(&list::null_definition())
        );
        assert_eq!(
            theory.computation(computation("is-singleton")),
            Some(&list::is_singleton_definition())
        );
        assert_eq!(reverse_acc(), Computation::Ref(computation("reverse_acc")));
        assert_eq!(reverse(), Computation::Ref(computation("reverse")));
        assert_eq!(append(), Computation::Ref(computation("append")));
        assert_eq!(snoc(), Computation::Ref(computation("snoc")));
        assert_eq!(concat(), Computation::Ref(computation("concat")));
        assert_eq!(last(), Computation::Ref(computation("last")));
        assert_eq!(init(), Computation::Ref(computation("init")));
        assert_eq!(null(), Computation::Ref(computation("null")));
        assert_eq!(
            is_singleton(),
            Computation::Ref(computation("is-singleton"))
        );
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

        for theorem in prelude_theorem_names() {
            assert!(theory.theorem(theorem).is_none());
            assert!(try_theory.theorem(theorem).is_none());
        }
    }

    #[test]
    fn computation_definition_diagnostics_report_kernel_rejection() {
        let mut theory = Theory::new();

        assert!(theory.define_computation(computation("reverse_acc"), &Computation::Nil));
        assert!(!define_computations_in_theory(&mut theory));
        assert_eq!(
            try_define_computations_in_theory(&mut theory),
            Err(SourceComputationError::ComputationRejected {
                computation: computation("reverse_acc"),
                error: ComputationDefinitionError::ComputationNameAlreadyDefined(computation(
                    "reverse_acc"
                )),
            })
        );
    }

    #[test]
    fn full_source_load_diagnostics_report_computation_failures() {
        let mut theory = Theory::new();

        assert!(theory.define_computation(computation("reverse_acc"), &Computation::Nil));
        assert!(!define_in_theory(&mut theory));
        assert_eq!(
            try_define_in_theory(&mut theory),
            Err(SourceLoadError::Computation(
                SourceComputationError::ComputationRejected {
                    computation: computation("reverse_acc"),
                    error: ComputationDefinitionError::ComputationNameAlreadyDefined(computation(
                        "reverse_acc"
                    )),
                }
            ))
        );
    }

    #[test]
    fn theorem_definitions_require_computations() {
        let mut theory = Theory::new();

        assert!(!define_theorems_in_theory(&mut theory));
        let Err(SourceTheoremError::ProofElaborationFailed {
            theorem: failed_theorem,
            error,
        }) = try_define_theorems_in_theory(&mut theory)
        else {
            panic!("theorem loading should report proof elaboration failure");
        };
        assert_eq!(failed_theorem, theorem("reverse_acc_computes_to_list"));
        assert!(proof_error_contains_evaluation_failure(&error));

        for theorem in prelude_theorem_names() {
            assert!(theory.theorem(theorem).is_none());
        }
    }

    #[test]
    fn full_source_load_diagnostics_report_theorem_failures() {
        let (module, env) = parse_test_module(
            "
            (theorem bad
              (equal nil (quote unit))
              (proof (eval-to nil nil)))
            ",
        );
        let bad = env
            .theorem("bad")
            .expect("module should define bad theorem");
        let mut theory = Theory::new();

        assert_eq!(
            define_module_in_theory_result(&mut theory, &module),
            Err(SourceLoadError::Theorem(
                SourceTheoremError::TheoremRejected {
                    theorem: bad,
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
        let (module, env) = parse_test_module(
            "
            (theorem bad
              (equal nil (quote unit))
              (proof (eval-to nil nil)))
            ",
        );
        let bad = env
            .theorem("bad")
            .expect("module should define bad theorem");

        assert_eq!(
            proof::source_theorem_result(module, bad, Theory::new()),
            Err(SourceTheoremError::TheoremRejected {
                theorem: bad,
                error: TheoremError::InvalidProof,
            })
        );
    }

    #[test]
    fn source_theorem_diagnostics_report_unknown_known_theorem() {
        let (module, env) = parse_test_module(
            "
            (theorem bad
              (equal nil nil)
              (proof (known later)))
            (theorem later
              (equal nil nil)
              (proof (eval-to nil nil)))
            ",
        );
        let bad = env
            .theorem("bad")
            .expect("module should define bad theorem");
        let later = env
            .theorem("later")
            .expect("module should define later theorem");

        assert_eq!(
            proof::source_theorem_result(module, bad, Theory::new()),
            Err(SourceTheoremError::ProofElaborationFailed {
                theorem: bad,
                error: ProofElaborationError::UnknownTheorem(later),
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
            theory.theorem(theorem("reverse_acc_computes_to_list")),
            Some(&reverse_acc_prop)
        );
        assert_eq!(
            theory.theorem(theorem("reverse_computes_to_list")),
            Some(&reverse_prop)
        );
        assert_eq!(
            theory.theorem(theorem("reverse_nil_computes_to_list")),
            Some(&reverse_nil_prop)
        );
        assert_eq!(
            theory.theorem(theorem("reverse_nil")),
            Some(&reverse_nil_exact_prop)
        );
        assert_eq!(
            theory.theorem(theorem("reverse_singleton")),
            Some(&reverse_singleton_prop)
        );
        assert_eq!(
            theory.theorem(theorem("reverse_acc_append")),
            Some(&reverse_acc_append_prop)
        );
        assert_eq!(
            theory.theorem(theorem("reverse_cons")),
            Some(&reverse_cons_prop)
        );
        assert_eq!(
            theory.theorem(theorem("reverse_acc_reverse")),
            Some(&reverse_acc_reverse_prop)
        );
        assert_eq!(
            theory.theorem(theorem("reverse_double")),
            Some(&reverse_double_prop)
        );
        assert_eq!(
            theory.theorem(theorem("reverse_acc_of_append")),
            Some(&reverse_acc_of_append_prop)
        );
        assert_eq!(
            theory.theorem(theorem("reverse_append")),
            Some(&reverse_append_prop)
        );
        assert_eq!(
            theory.theorem(theorem("snoc_computes_to_list")),
            Some(&snoc_prop)
        );
        assert_eq!(theory.theorem(theorem("snoc_nil")), Some(&snoc_nil_prop));
        assert_eq!(theory.theorem(theorem("snoc_cons")), Some(&snoc_cons_prop));
        assert_eq!(
            theory.theorem(theorem("concat_nil")),
            Some(&concat_nil_prop)
        );
        assert_eq!(
            theory.theorem(theorem("last_nil_errors")),
            Some(&last_nil_errors_prop)
        );
        assert_eq!(
            theory.theorem(theorem("last_singleton")),
            Some(&last_singleton_prop)
        );
        assert_eq!(theory.theorem(theorem("last_cons")), Some(&last_cons_prop));
        assert_eq!(
            theory.theorem(theorem("init_nil_errors")),
            Some(&init_nil_errors_prop)
        );
        assert_eq!(
            theory.theorem(theorem("init_singleton")),
            Some(&init_singleton_prop)
        );
        assert_eq!(theory.theorem(theorem("init_cons")), Some(&init_cons_prop));
        assert_eq!(theory.theorem(theorem("null_nil")), Some(&null_nil_prop));
        assert_eq!(theory.theorem(theorem("null_cons")), Some(&null_cons_prop));
        assert_eq!(
            theory.theorem(theorem("is_singleton_nil")),
            Some(&is_singleton_nil_prop)
        );
        assert_eq!(
            theory.theorem(theorem("is_singleton_singleton")),
            Some(&is_singleton_singleton_prop)
        );
        assert_eq!(
            theory.theorem(theorem("is_singleton_cons")),
            Some(&is_singleton_cons_prop)
        );
        assert_eq!(
            theory.theorem(theorem("append_nil_computes_to_list")),
            Some(&append_nil_prop)
        );
        assert_eq!(
            theory.theorem(theorem("append_computes_to_list")),
            Some(&append_prop)
        );
        assert_eq!(
            theory.theorem(theorem("append_nil_returns_right")),
            Some(&append_nil_returns_right_prop)
        );
        assert_eq!(
            theory.theorem(theorem("append_right_nil")),
            Some(&append_right_nil_prop)
        );
        assert_eq!(
            theory.theorem(theorem("append_cons")),
            Some(&append_cons_prop)
        );
        assert_eq!(
            theory.theorem(theorem("append_singleton")),
            Some(&append_singleton_prop)
        );
        assert_eq!(
            theory.theorem(theorem("append_assoc")),
            Some(&append_assoc_prop)
        );
        assert_eq!(
            theory
                .known(theorem("reverse_computes_to_list"))
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
            .known(theorem("reverse_computes_to_list"))
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
