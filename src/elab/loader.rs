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

        assert_eq!(
            loaded.theory().computation(id),
            Some(&Computation::Lambda(crate::Lambda {
                parameter: crate::Symbol(1),
                body: Box::new(Computation::Var(crate::Symbol(1))),
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
