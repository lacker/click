//! Source loading into a checked theory.

use std::{
    fs, io,
    path::{Path, PathBuf},
};

use crate::{ComputationDefinitionError, Name, Symbol, Theory};

use super::{
    proof::{self, SourceTheoremError},
    source::{ElabEnv, ParseError, ParsedModule},
};

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

#[derive(Debug)]
pub enum SourceFileLoadError {
    ReadFailed { path: PathBuf, error: io::Error },
    SourceLoadFailed(SourceLoadError),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoadedSource {
    theory: Theory,
    env: ElabEnv,
    modules: Vec<ParsedModule>,
}

impl Default for LoadedSource {
    fn default() -> Self {
        Self::new()
    }
}

impl LoadedSource {
    pub fn new() -> Self {
        Self::with_env(ElabEnv::new())
    }

    pub fn with_env(env: ElabEnv) -> Self {
        Self {
            theory: Theory::new(),
            env,
            modules: Vec::new(),
        }
    }

    pub fn theory(&self) -> &Theory {
        &self.theory
    }

    pub fn env(&self) -> &ElabEnv {
        &self.env
    }

    pub fn into_theory(self) -> Theory {
        self.theory
    }

    pub fn computation(&self, spelling: &str) -> Option<Name> {
        self.env.computation(spelling)
    }

    pub fn theorem(&self, spelling: &str) -> Option<Name> {
        self.env.theorem(spelling)
    }

    pub fn symbol(&self, spelling: &str) -> Option<Symbol> {
        self.env.symbol(spelling)
    }

    pub fn load_str(&mut self, source: &str) -> Result<(), SourceLoadError> {
        let mut env = self.env.clone();
        let module = env
            .parse_module(source)
            .map_err(SourceLoadError::ModuleParseFailed)?;
        let mut theory = self.theory.clone();

        define_module_computations_result(&mut theory, &module)
            .map_err(SourceLoadError::Computation)?;
        define_module_theorems_result(&mut theory, &module).map_err(SourceLoadError::Theorem)?;

        self.env = env;
        self.theory = theory;
        self.modules.push(module);

        Ok(())
    }

    pub fn load_file(&mut self, path: impl AsRef<Path>) -> Result<(), SourceFileLoadError> {
        let path = path.as_ref();
        let source = fs::read_to_string(path).map_err(|error| SourceFileLoadError::ReadFailed {
            path: path.to_path_buf(),
            error,
        })?;

        self.load_str(&source)
            .map_err(SourceFileLoadError::SourceLoadFailed)
    }

    pub fn load_computations_str(&mut self, source: &str) -> Result<(), SourceComputationError> {
        let mut env = self.env.clone();
        let module = env
            .parse_module(source)
            .map_err(SourceComputationError::ModuleParseFailed)?;
        let mut theory = self.theory.clone();

        define_module_computations_result(&mut theory, &module)?;

        self.env = env;
        self.theory = theory;
        self.modules.push(module);

        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn module(&self, index: usize) -> Option<&ParsedModule> {
        self.modules.get(index)
    }

    pub(crate) fn modules(&self) -> &[ParsedModule] {
        &self.modules
    }
}

pub(crate) fn define_module_computations_result(
    theory: &mut Theory,
    module: &ParsedModule,
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

pub(crate) fn define_module_theorems_result(
    theory: &mut Theory,
    module: &ParsedModule,
) -> Result<(), SourceTheoremError> {
    for theorem in &module.theorems {
        proof::define_source_theorem(theorem, theory)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Computation, computes_to};

    #[test]
    fn load_str_defines_computations_and_theorems() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str(
                "
                (def id (lambda x x))
                (theorem id_nil
                  (computes-to (id nil) nil)
                  (proof (eval-to (id nil) nil)))
                ",
            )
            .expect("source should load");

        let id = loaded
            .computation("id")
            .expect("loader should record computation spelling");
        let id_nil = loaded
            .theorem("id_nil")
            .expect("loader should record theorem spelling");

        let parameter = crate::Symbol(crate::LIST_KIND_SYMBOL.0 + 1);

        assert_eq!(
            loaded.theory().computation(id),
            Some(&Computation::Lambda(crate::Lambda {
                parameter,
                body: Box::new(Computation::Var(parameter)),
            }))
        );
        assert_eq!(
            loaded.theory().theorem(id_nil),
            Some(&computes_to(
                Computation::Apply {
                    function: Box::new(Computation::Ref(id)),
                    argument: Box::new(Computation::Nil),
                },
                Computation::Nil
            ))
        );
    }

    #[test]
    fn load_str_checks_if_theorems() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str(
                "
                (def choose (if (quote :true) nil diverge))
                (theorem choose_nil
                  (computes-to choose nil)
                  (proof (eval-to choose nil)))
                ",
            )
            .expect("source if theorem should load");

        let choose = loaded
            .computation("choose")
            .expect("loader should record if computation spelling");
        let choose_nil = loaded
            .theorem("choose_nil")
            .expect("loader should record if theorem spelling");

        assert_eq!(
            loaded.theory().computation(choose),
            Some(&crate::if_then_else(
                Computation::Quote(crate::TRUE_SYMBOL),
                Computation::Nil,
                Computation::Diverge,
            ))
        );
        assert_eq!(
            loaded.theory().theorem(choose_nil),
            Some(&computes_to(Computation::Ref(choose), Computation::Nil))
        );
    }

    #[test]
    fn load_str_checks_by_tactic_theorems() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str(
                "
                (def id (lambda x x))
                (theorem id_computes
                  (forall value (is-value value)
                    (computes-to (id value) value))
                  (by
                    (intro value)
                    (eval)))
                (theorem id_nil
                  (computes-to (id nil) nil)
                  (by
                    (apply id_computes nil)))
                (theorem id_id_nil
                  (computes-to (id (id nil)) nil)
                  (by
                    (calc
                      (id (id nil))
                      (== (id nil) (by (eval)))
                      (== nil (by (eval))))))
                (theorem id_rewrite_nil
                  (forall value (is-value value)
                    (implies
                      (computes-to value nil)
                      (computes-to (id value) nil)))
                  (by
                    (intro value)
                    (intro value_nil)
                    (rewrite value_nil)
                    (eval)))
                (theorem value_self
                  (forall value (is-value value)
                    (computes-to value value))
                  (by
                    (intro value)
                    (eval)))
                (theorem nil_via_have
                  (computes-to nil nil)
                  (by
                    (have nil_self
                      (computes-to nil nil)
                      (by
                        (exact value_self nil)))
                    (rewrite (value_self nil))
                    (exact nil_self)))
                (theorem nil_via_have_body
                  (computes-to nil nil)
                  (by
                    (have nil_self
                      (computes-to nil nil)
                      (by
                        (exact value_self nil))
                      (by
                        (exact nil_self)))))
                (theorem nil_via_specialize
                  (computes-to nil nil)
                  (by
                    (specialize nil_self value_self nil)
                    (exact nil_self)))
                (theorem nil_via_symm_application
                  (computes-to nil nil)
                  (by
                    (exact (symm (value_self nil)))))
                (theorem list_exists
                  (exists result (is-list result)
                    (computes-to nil result))
                  (by
                    (exists nil
                      (by
                        (eval)))))
                (theorem nil_from_obtain_body
                  (computes-to nil nil)
                  (by
                    (obtain witness witness_proof list_exists
                      (by
                        (exact
                          (trans
                            (assume witness_proof)
                            (symm
                              (assume witness_proof))))))))
                (theorem nil_from_obtain
                  (computes-to nil nil)
                  (by
                    (obtain witness witness_proof list_exists)
                    (exact
                      (trans
                        (assume witness_proof)
                        (symm
                          (assume witness_proof))))))
                (theorem nil_pair
                  (and
                    (computes-to nil nil)
                    (computes-to nil nil))
                  (by
                    (split
                      (by
                        (eval))
                      (by
                        (eval)))))
                (theorem nil_from_cases
                  (computes-to nil nil)
                  (by
                    (cases nil_pair nil_left nil_right)
                    (exact nil_left)))
                (theorem list_self
                  (forall list (is-list list)
                    (computes-to list list))
                  (by
                    (list-induction list
                      (by
                        (eval))
                      head
                      tail
                      ih
                      (by
                        (eval)))))
                (theorem nil_exact
                  (computes-to nil nil)
                  (by
                    (exact (eval-to nil nil))))
                (theorem nil_identity
                  (implies
                    (computes-to nil nil)
                    (computes-to nil nil))
                  (by
                    (intro h)
                    (assumption)))
                (theorem nil_identity_apply
                  (implies
                    (computes-to nil nil)
                    (computes-to nil nil))
                  (by
                    (intro h)
                    (apply nil_identity)))
                ",
            )
            .expect("source tactic theorems should load");

        let id_nil = loaded
            .theorem("id_nil")
            .expect("loader should record tactic theorem spelling");
        let id_id_nil = loaded
            .theorem("id_id_nil")
            .expect("loader should record calc tactic theorem spelling");
        let id_rewrite_nil = loaded
            .theorem("id_rewrite_nil")
            .expect("loader should record rewrite tactic theorem spelling");
        let nil_via_have = loaded
            .theorem("nil_via_have")
            .expect("loader should record have tactic theorem spelling");
        let nil_via_have_body = loaded
            .theorem("nil_via_have_body")
            .expect("loader should record explicit have body theorem spelling");
        let nil_via_specialize = loaded
            .theorem("nil_via_specialize")
            .expect("loader should record specialize tactic theorem spelling");
        let nil_via_symm_application = loaded
            .theorem("nil_via_symm_application")
            .expect("loader should record symm proof application theorem spelling");
        let nil_from_obtain_body = loaded
            .theorem("nil_from_obtain_body")
            .expect("loader should record explicit obtain body theorem spelling");
        let nil_from_obtain = loaded
            .theorem("nil_from_obtain")
            .expect("loader should record obtain tactic theorem spelling");
        let nil_pair = loaded
            .theorem("nil_pair")
            .expect("loader should record conjunction tactic theorem spelling");
        let nil_from_cases = loaded
            .theorem("nil_from_cases")
            .expect("loader should record cases tactic theorem spelling");
        let list_self = loaded
            .theorem("list_self")
            .expect("loader should record induction tactic theorem spelling");
        let id = loaded.computation("id").expect("id should be loaded");

        assert_eq!(
            loaded.theory().theorem(id_nil),
            Some(&computes_to(
                Computation::Apply {
                    function: Box::new(Computation::Ref(id)),
                    argument: Box::new(Computation::Nil),
                },
                Computation::Nil
            ))
        );
        assert_eq!(
            loaded.theory().theorem(id_id_nil),
            Some(&computes_to(
                Computation::Apply {
                    function: Box::new(Computation::Ref(id)),
                    argument: Box::new(Computation::Apply {
                        function: Box::new(Computation::Ref(id)),
                        argument: Box::new(Computation::Nil),
                    }),
                },
                Computation::Nil
            ))
        );
        assert!(loaded.theory().theorem(id_rewrite_nil).is_some());
        assert!(loaded.theory().theorem(nil_via_have).is_some());
        assert!(loaded.theory().theorem(nil_via_have_body).is_some());
        assert!(loaded.theory().theorem(nil_via_specialize).is_some());
        assert!(loaded.theory().theorem(nil_via_symm_application).is_some());
        assert!(loaded.theory().theorem(nil_from_obtain_body).is_some());
        assert!(loaded.theory().theorem(nil_from_obtain).is_some());
        assert!(loaded.theory().theorem(nil_pair).is_some());
        assert!(loaded.theory().theorem(nil_from_cases).is_some());
        assert!(loaded.theory().theorem(list_self).is_some());
    }

    #[test]
    fn load_str_checks_structured_by_tactics() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str(
                "
                (theorem nil_result
                  (computes-to-list result nil)
                  (by
                    (exists nil
                      (by
                        (eval)))))
                (theorem split_or
                  (and
                    (computes-to nil nil)
                    (or
                      (computes-to nil nil)
                      (computes-to diverge diverge)))
                  (by
                    (split
                      (by
                        (eval))
                      (by
                        (left
                          (by
                            (eval)))))))
                (theorem constructor_right
                  (and
                    (computes-to nil nil)
                    (or
                      (computes-to diverge diverge)
                      (computes-to nil nil)))
                  (by
                    (constructor
                      (by
                        (eval))
                      (by
                        (right
                          (by
                            (eval)))))))
                (theorem nil_or_diverge
                  (or
                    (computes-to nil nil)
                    (computes-to diverge diverge))
                  (by
                    (left
                      (by
                        (eval)))))
                (theorem nil_from_or
                  (computes-to nil nil)
                  (by
                    (or-elim
                      nil_or_diverge
                      nil_case
                      (by
                        (exact nil_case))
                      diverge_case
                      (by
                        (eval)))))
                ",
            )
            .expect("structured tactic theorems should load");

        assert!(loaded.theorem("nil_result").is_some());
        assert!(loaded.theorem("split_or").is_some());
        assert!(loaded.theorem("constructor_right").is_some());
        assert!(loaded.theorem("nil_or_diverge").is_some());
        assert!(loaded.theorem("nil_from_or").is_some());
    }

    #[test]
    fn load_str_checks_symbol_eq_is_bool_theorems() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str(
                "
                (def same (symbol-eq (quote :true) (quote :false)))
                (theorem same_is_bool
                  (is-bool same)
                  (proof
                    (or-intro-right
                      (computes-to same (quote :true))
                      (eval-to same (quote :false)))))
                ",
            )
            .expect("source symbol-eq bool theorem should load");

        let same = loaded
            .computation("same")
            .expect("loader should record symbol-eq computation spelling");
        let same_is_bool = loaded
            .theorem("same_is_bool")
            .expect("loader should record is-bool theorem spelling");

        assert_eq!(
            loaded.theory().computation(same),
            Some(&crate::symbol_eq(
                Computation::Quote(crate::TRUE_SYMBOL),
                Computation::Quote(crate::FALSE_SYMBOL),
            ))
        );
        assert_eq!(
            loaded.theory().theorem(same_is_bool),
            Some(&crate::is_bool(Computation::Ref(same)))
        );
    }

    #[test]
    fn load_str_checks_absurd_and_if_condition_bool_theorems() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str(
                "
                (theorem condition_is_bool
                  (is-bool (quote :true))
                  (proof
                    (if-value-condition-bool
                      (eval-to
                        (if (quote :true) nil (error 0))
                        nil))))
                (theorem assumed_distinct_outcomes_are_absurd
                  (implies
                    (equal (quote :true) (quote :false))
                    (absurd))
                  (proof
                    (implies-intro impossible
                      (equal (quote :true) (quote :false))
                      (distinct-outcomes
                        (assume impossible)))))
                (theorem absurd_eliminates
                  (implies
                    (equal (quote :true) (quote :false))
                    (is-value nil))
                  (proof
                    (implies-intro impossible
                      (equal (quote :true) (quote :false))
                      (absurd-elim
                        (distinct-outcomes
                          (assume impossible))
                        (is-value nil)))))
                ",
            )
            .expect("source absurd and if condition bool theorems should load");

        let condition_is_bool = loaded
            .theorem("condition_is_bool")
            .expect("loader should record condition bool theorem spelling");
        let assumed_distinct_outcomes_are_absurd = loaded
            .theorem("assumed_distinct_outcomes_are_absurd")
            .expect("loader should record absurd theorem spelling");
        let absurd_eliminates = loaded
            .theorem("absurd_eliminates")
            .expect("loader should record absurd elimination theorem spelling");

        let contradiction = crate::equal(
            Computation::Quote(crate::TRUE_SYMBOL),
            Computation::Quote(crate::FALSE_SYMBOL),
        );
        assert_eq!(
            loaded.theory().theorem(condition_is_bool),
            Some(&crate::is_bool(Computation::Quote(crate::TRUE_SYMBOL)))
        );
        assert_eq!(
            loaded
                .theory()
                .theorem(assumed_distinct_outcomes_are_absurd),
            Some(&crate::implies(contradiction.clone(), crate::absurd()))
        );
        assert_eq!(
            loaded.theory().theorem(absurd_eliminates),
            Some(&crate::implies(
                contradiction,
                crate::is_value(Computation::Nil)
            ))
        );
    }

    #[test]
    fn load_str_checks_value_kind_theorems() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str(
                "
                (def list_kind (value-kind nil))
                (theorem list_kind_is_list
                  (computes-to list_kind (quote :list))
                  (proof
                    (eval-to list_kind (quote :list))))
                ",
            )
            .expect("source value-kind theorem should load");

        let list_kind = loaded
            .computation("list_kind")
            .expect("loader should record value-kind computation spelling");
        let list_kind_is_list = loaded
            .theorem("list_kind_is_list")
            .expect("loader should record value-kind theorem spelling");

        assert_eq!(
            loaded.theory().computation(list_kind),
            Some(&crate::value_kind(Computation::Nil))
        );
        assert_eq!(
            loaded.theory().theorem(list_kind_is_list),
            Some(&crate::computes_to(
                Computation::Ref(list_kind),
                Computation::Quote(crate::LIST_KIND_SYMBOL),
            ))
        );
    }

    #[test]
    fn load_str_checks_source_or_proof_forms() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str(
                "
                (theorem or_elim_example
                  (equal nil nil)
                  (proof
                    (or-elim
                      (or-intro-left
                        (eval-to nil nil)
                        (equal nil nil))
                      left_case
                      (assume left_case)
                      right_case
                      (assume right_case))))
                ",
            )
            .expect("source or proof forms should load");

        let theorem = loaded
            .theorem("or_elim_example")
            .expect("loader should record or theorem spelling");

        assert_eq!(
            loaded.theory().theorem(theorem),
            Some(&crate::equal(Computation::Nil, Computation::Nil))
        );
    }

    #[test]
    fn load_str_does_not_commit_failed_modules() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str("(def id (lambda x x))")
            .expect("first module should load");
        let id = loaded.computation("id");
        let error = loaded.load_str(
            "
            (def bad nil)
            (theorem bad_theorem
              (equal nil nil)
              (proof (known missing)))
            ",
        );

        assert!(error.is_err());
        assert_eq!(loaded.computation("id"), id);
        assert_eq!(loaded.computation("bad"), None);
        assert_eq!(loaded.theorem("bad_theorem"), None);
    }

    #[test]
    fn specialize_missing_premise_reports_context() {
        let mut loaded = LoadedSource::new();

        let error = loaded
            .load_str(
                "
                (theorem gated_forall
                  (forall left (is-list left)
                    (implies
                      (computes-to (head left) nil)
                      (forall right (is-list right)
                        (equal right right))))
                  (proof
                    (forall-intro left (is-list left)
                      (implies-intro left_head_nil
                        (computes-to (head left) nil)
                        (forall-intro right (is-list right)
                          (eval-to right right))))))
                (theorem bad_specialize
                  (implies
                    (computes-to nil nil)
                    (equal nil nil))
                  (by
                    (intro nil_self)
                    (specialize bad gated_forall nil nil)
                    (exact nil_self)))
                ",
            )
            .expect_err("specialize should report the unavailable premise");

        let SourceLoadError::Theorem(SourceTheoremError::ProofElaborationFailed {
            error: proof::ProofElaborationError::TacticFailed { tactic, message },
            ..
        }) = error
        else {
            panic!("expected a specialize tactic failure");
        };

        assert_eq!(tactic, "specialize");
        assert!(message.contains("premise"));
        assert!(message.contains("is not available"));
        assert!(message.contains("local facts in scope"));
        assert!(message.contains("nil_self") || message.contains("Symbol("));
    }

    #[test]
    fn load_file_reads_source_from_disk() {
        let mut loaded = LoadedSource::new();
        let path = std::env::temp_dir().join(format!(
            "click-loaded-source-{}-{}.lisp",
            std::process::id(),
            "load-file"
        ));

        fs::write(&path, "(def file_id (lambda x x))").expect("test file should be written");
        let result = loaded.load_file(&path);
        let _ = fs::remove_file(&path);

        result.expect("file source should load");
        assert!(loaded.computation("file_id").is_some());
    }
}
