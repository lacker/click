//! Source loading into a checked theory.

use std::{
    fs, io,
    path::{Path, PathBuf},
};

use crate::{ComputationDefinitionError, Name, Symbol, Theory};

use super::{
    proof::{self, SourceTheoremError},
    source::{ElabEnv, ParseError, ParsedModule, SourceSection},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceComputationError {
    ModuleParseFailed {
        section: Option<SourceSection>,
        error: ParseError,
    },
    ComputationRejected {
        section: Option<SourceSection>,
        computation: Name,
        error: ComputationDefinitionError,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceLoadError {
    ModuleParseFailed {
        section: Option<SourceSection>,
        error: ParseError,
    },
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
    modules: Vec<LoadedModule>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LoadedModule {
    section: Option<SourceSection>,
    module: ParsedModule,
}

impl LoadedModule {
    fn new(section: Option<SourceSection>, module: ParsedModule) -> Self {
        Self { section, module }
    }

    pub(crate) fn section(&self) -> Option<&SourceSection> {
        self.section.as_ref()
    }

    pub(crate) fn parsed(&self) -> &ParsedModule {
        &self.module
    }
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
        self.load_str_in_section(None, source)
    }

    pub fn load_section(
        &mut self,
        section: impl Into<SourceSection>,
        source: &str,
    ) -> Result<(), SourceLoadError> {
        self.load_str_in_section(Some(section.into()), source)
    }

    fn load_str_in_section(
        &mut self,
        section: Option<SourceSection>,
        source: &str,
    ) -> Result<(), SourceLoadError> {
        let mut env = self.env.clone();
        let module =
            env.parse_module(source)
                .map_err(|error| SourceLoadError::ModuleParseFailed {
                    section: section.clone(),
                    error,
                })?;
        let mut theory = self.theory.clone();

        define_module_computations_result_in_section(&mut theory, &module, section.as_ref())
            .map_err(SourceLoadError::Computation)?;
        define_module_theorems_result_in_section(&mut theory, &module, section.as_ref())
            .map_err(SourceLoadError::Theorem)?;

        self.env = env;
        self.theory = theory;
        self.modules.push(LoadedModule::new(section, module));

        Ok(())
    }

    pub fn load_file(&mut self, path: impl AsRef<Path>) -> Result<(), SourceFileLoadError> {
        let path = path.as_ref();
        let source = fs::read_to_string(path).map_err(|error| SourceFileLoadError::ReadFailed {
            path: path.to_path_buf(),
            error,
        })?;

        let section = SourceSection::new(path.display().to_string());
        self.load_section(section, &source)
            .map_err(SourceFileLoadError::SourceLoadFailed)
    }

    pub fn load_computations_str(&mut self, source: &str) -> Result<(), SourceComputationError> {
        self.load_computations_str_in_section(None, source)
    }

    pub fn load_computations_section(
        &mut self,
        section: impl Into<SourceSection>,
        source: &str,
    ) -> Result<(), SourceComputationError> {
        self.load_computations_str_in_section(Some(section.into()), source)
    }

    fn load_computations_str_in_section(
        &mut self,
        section: Option<SourceSection>,
        source: &str,
    ) -> Result<(), SourceComputationError> {
        let mut env = self.env.clone();
        let module = env.parse_module(source).map_err(|error| {
            SourceComputationError::ModuleParseFailed {
                section: section.clone(),
                error,
            }
        })?;
        let mut theory = self.theory.clone();

        define_module_computations_result_in_section(&mut theory, &module, section.as_ref())?;

        self.env = env;
        self.theory = theory;
        self.modules.push(LoadedModule::new(section, module));

        Ok(())
    }

    pub(crate) fn modules(&self) -> &[LoadedModule] {
        &self.modules
    }
}

#[cfg(test)]
pub(crate) fn define_module_computations_result(
    theory: &mut Theory,
    module: &ParsedModule,
) -> Result<(), SourceComputationError> {
    define_module_computations_result_in_section(theory, module, None)
}

pub(crate) fn define_module_computations_result_in_section(
    theory: &mut Theory,
    module: &ParsedModule,
    section: Option<&SourceSection>,
) -> Result<(), SourceComputationError> {
    for (name, computation) in &module.computations {
        theory
            .define_computation_result(*name, computation)
            .map_err(|error| SourceComputationError::ComputationRejected {
                section: section.cloned(),
                computation: *name,
                error,
            })?;
    }

    Ok(())
}

#[cfg(test)]
pub(crate) fn define_module_theorems_result(
    theory: &mut Theory,
    module: &ParsedModule,
) -> Result<(), SourceTheoremError> {
    define_module_theorems_result_in_section(theory, module, None)
}

pub(crate) fn define_module_theorems_result_in_section(
    theory: &mut Theory,
    module: &ParsedModule,
    section: Option<&SourceSection>,
) -> Result<(), SourceTheoremError> {
    for theorem in &module.theorems {
        proof::define_source_theorem_with_section(theorem, theory, section)?;
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
    fn load_section_records_section_and_reports_failures() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_section(
                "test/good",
                "
                (def id (lambda x x))
                ",
            )
            .expect("named source section should load");

        assert_eq!(
            loaded.modules()[0].section(),
            Some(&SourceSection::new("test/good"))
        );

        let error = loaded
            .load_section(
                "test/bad",
                "
                (theorem bad
                  (equal nil (quote unit))
                  (proof (eval-to nil nil)))
                ",
            )
            .expect_err("bad source section should report its name");

        let SourceLoadError::Theorem(SourceTheoremError::TheoremRejected {
            section, error, ..
        }) = error
        else {
            panic!("expected a sectioned theorem rejection");
        };

        assert_eq!(section, Some(SourceSection::new("test/bad")));
        assert_eq!(error, crate::TheoremError::InvalidProof);
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
    fn load_str_checks_simp_tactic_theorems() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str(
                "
                (theorem rewrite_value_nil
                  (forall value (is-value value)
                    (implies
                      (computes-to value nil)
                      (computes-to value nil)))
                  (by
                    (intro value)
                    (intro value_nil)
                    (exact value_nil)))
                (theorem simp_rewrites_value_nil
                  (forall value (is-value value)
                    (implies
                      (computes-to value nil)
                      (computes-to value nil)))
                  (by
                    (intro value)
                    (intro value_nil)
                    (simp only rewrite_value_nil)))
                (theorem simp_uses_local_condition
                  (forall condition (is-value condition)
                    (implies
                      (computes-to condition (quote :true))
                      (computes-to
                        (if condition nil (error 0))
                        nil)))
                  (by
                    (intro condition)
                    (intro condition_true)
                    (simp only condition_true)))
                (theorem simp_uses_conjunction_condition
                  (forall condition
                    (and
                      (is-value condition)
                      (computes-to condition (quote :true)))
                    (computes-to
                      (if condition nil (error 0))
                      nil))
                  (by
                    (intro condition)
                    (simp only condition)))
                (theorem simpa_uses_local_proof
                  (forall value (is-value value)
                    (implies
                      (computes-to value nil)
                      (computes-to
                        (if (quote :true) value (error 0))
                        nil)))
                  (by
                    (intro value)
                    (intro value_nil)
                    (simpa only using value_nil)))
                ",
            )
            .expect("source simp theorem should load");

        assert!(loaded.theorem("rewrite_value_nil").is_some());
        assert!(loaded.theorem("simp_rewrites_value_nil").is_some());
        assert!(loaded.theorem("simp_uses_local_condition").is_some());
        assert!(loaded.theorem("simp_uses_conjunction_condition").is_some());
        assert!(loaded.theorem("simpa_uses_local_proof").is_some());
    }

    #[test]
    fn load_str_checks_fold_tactic_theorems() {
        let mut loaded = LoadedSource::new();

        loaded
            .load_str(
                "
                (def alias nil)
                (theorem fold_alias_nil
                  (equal nil alias)
                  (by
                    (fold alias)
                    (eval)))
                ",
            )
            .expect("source fold theorem should load");

        assert!(loaded.theorem("fold_alias_nil").is_some());
    }

    #[test]
    fn failing_rewrite_reports_non_equality_proof_and_goal() {
        let mut loaded = LoadedSource::new();

        let error = loaded
            .load_str(
                "
                (theorem nil_is_value
                  (is-value nil)
                  (proof
                    (primitive (is-value nil))))
                (theorem bad_rewrite
                  (equal nil nil)
                  (by
                    (rewrite nil_is_value)
                    (eval)))
                ",
            )
            .expect_err("rewrite with a non-equality proof should fail");

        let SourceLoadError::Theorem(SourceTheoremError::ProofElaborationFailed {
            error: proof::ProofElaborationError::TacticFailed { tactic, message },
            ..
        }) = error
        else {
            panic!("expected a rewrite tactic failure");
        };

        assert_eq!(tactic, "rewrite");
        assert!(message.contains("rewrite proof is not an equality"));
        assert!(message.contains("current goal"));
        assert!(message.contains("proof produced"));
        assert!(message.contains("expected: an equality"));
    }

    #[test]
    fn failing_rewrite_reports_reverse_direction_hint() {
        let mut loaded = LoadedSource::new();

        let error = loaded
            .load_str(
                "
                (def alias nil)
                (theorem alias_nil
                  (equal alias nil)
                  (by
                    (eval)))
                (theorem bad_rewrite
                  (equal nil nil)
                  (by
                    (rewrite alias_nil)
                    (eval)))
                ",
            )
            .expect_err("rewrite with the equality in the wrong direction should fail");

        let SourceLoadError::Theorem(SourceTheoremError::ProofElaborationFailed {
            error: proof::ProofElaborationError::TacticFailed { tactic, message },
            ..
        }) = error
        else {
            panic!("expected a rewrite tactic failure");
        };

        assert_eq!(tactic, "rewrite");
        assert!(message.contains("goal does not contain the rewrite left side"));
        assert!(message.contains("current goal"));
        assert!(message.contains("equality left side searched for"));
        assert!(message.contains("equality right side"));
        assert!(message.contains("try `(rewrite (symm ...))`"));
    }

    #[test]
    fn failing_simp_reports_simplification_steps() {
        let mut loaded = LoadedSource::new();

        let error = loaded
            .load_str(
                "
                (theorem bad_simp
                  (equal
                    (if (quote :true) nil (error 0))
                    (error 1))
                  (by
                    (simp only)))
                ",
            )
            .expect_err("bad simp theorem should report a useful failure");

        let SourceLoadError::Theorem(SourceTheoremError::ProofElaborationFailed {
            error: proof::ProofElaborationError::TacticFailed { tactic, message },
            ..
        }) = error
        else {
            panic!("expected a simp tactic failure");
        };

        assert_eq!(tactic, "simp");
        assert!(message.contains("simplified goal, but the sides still differ"));
        assert!(message.contains("left original"));
        assert!(message.contains("left result"));
        assert!(message.contains("left steps"));
        assert!(message.contains("kernel reduction"));
        assert!(message.contains("right steps"));
        assert!(message.contains("(no simplification steps)"));
    }

    #[test]
    fn failing_simp_reports_expansion_oriented_rules() {
        let mut loaded = LoadedSource::new();

        let error = loaded
            .load_str(
                "
                (def alias nil)
                (theorem alias_nil
                  (equal alias nil)
                  (by
                    (eval)))
                (theorem bad_simp_cycle
                  (equal nil nil)
                  (by
                    (simp only (symm alias_nil))))
                ",
            )
            .expect_err("expansion-oriented simp rule should be rejected");

        let SourceLoadError::Theorem(SourceTheoremError::ProofElaborationFailed {
            error: proof::ProofElaborationError::TacticFailed { tactic, message },
            ..
        }) = error
        else {
            panic!("expected a simp tactic failure");
        };

        assert_eq!(tactic, "simp");
        assert!(message.contains("oriented as an expansion"));
        assert!(message.contains("immediately undone by kernel reduction"));
        assert!(message.contains("fold <definition>"));
        assert!(message.contains("rewrite`/`eval"));
        assert!(message.contains("canonical forms"));
        assert!(message.contains("Symm"));
        assert!(message.contains("kernel reduction"));
    }

    #[test]
    fn failing_simpa_reports_expansion_oriented_rules_as_simpa() {
        let mut loaded = LoadedSource::new();

        let error = loaded
            .load_str(
                "
                (def alias nil)
                (theorem alias_nil
                  (equal alias nil)
                  (by
                    (eval)))
                (theorem bad_simpa_cycle
                  (equal nil nil)
                  (by
                    (simpa only (symm alias_nil))))
                ",
            )
            .expect_err("expansion-oriented simpa rule should be rejected");

        let SourceLoadError::Theorem(SourceTheoremError::ProofElaborationFailed {
            error: proof::ProofElaborationError::TacticFailed { tactic, message },
            ..
        }) = error
        else {
            panic!("expected a simpa tactic failure");
        };

        assert_eq!(tactic, "simpa");
        assert!(message.contains("oriented as an expansion"));
        assert!(message.contains("fold <definition>"));
        assert!(message.contains("immediately undone by kernel reduction"));
        assert!(message.contains("canonical forms"));
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
    fn proof_application_rejects_explicit_proof_premise_with_hint() {
        let mut loaded = LoadedSource::new();

        let error = loaded
            .load_str(
                "
                (theorem implication
                  (implies
                    (equal nil nil)
                    (equal nil nil))
                  (by
                    (intro nil_self)
                    (exact nil_self)))
                (theorem bad_exact
                  (implies
                    (equal nil nil)
                    (equal nil nil))
                  (by
                    (intro nil_self)
                    (exact implication nil_self)))
                ",
            )
            .expect_err("proof application should reject explicit proof premise");

        let SourceLoadError::Theorem(SourceTheoremError::ProofElaborationFailed {
            error: proof::ProofElaborationError::TacticFailed { tactic, message },
            ..
        }) = error
        else {
            panic!("expected a proof application tactic failure");
        };

        assert_eq!(tactic, "proof application");
        assert!(message.contains("explicit computation arguments"));
        assert!(message.contains("implication premise"));
        assert!(message.contains("forall-bound computations"));
        assert!(message.contains("applied automatically"));
        assert!(message.contains("local proof/fact"));
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
