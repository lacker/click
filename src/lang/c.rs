//! A tiny C0 language model used to drive Click toward C proofs.

use std::sync::OnceLock;

use crate::{
    Name, Symbol, Theory,
    elab::{
        LoadedSource, SourceComputationError, SourceLoadError, SourceTheoremError,
        loader::{
            define_module_computations_result_in_section, define_module_theorems_result_in_section,
        },
    },
};

#[cfg(test)]
use crate::elab::{SourceEnv, loader::LoadedModule, source};

const CORE_SOURCE: &str = include_str!("c/core.lisp");

const SOURCES: &[(&str, &str)] = &[("lang/c/core", CORE_SOURCE)];

static LOADED_C: OnceLock<Result<LoadedSource, SourceLoadError>> = OnceLock::new();
static LOADED_C_COMPUTATIONS: OnceLock<Result<LoadedSource, SourceLoadError>> = OnceLock::new();

pub type LoadedC = LoadedSource;

pub fn loaded() -> LoadedC {
    try_loaded().expect("C source model should define a valid theory")
}

pub fn try_loaded() -> Result<LoadedC, SourceLoadError> {
    loaded_source().cloned()
}

pub fn computation_name(spelling: &str) -> Option<Name> {
    loaded_source().ok()?.computation(spelling)
}

pub fn theorem_name(spelling: &str) -> Option<Name> {
    loaded_source().ok()?.theorem(spelling)
}

pub fn symbol_name(spelling: &str) -> Option<Symbol> {
    loaded_source().ok()?.symbol(spelling)
}

pub fn theory() -> Theory {
    loaded().into_theory()
}

pub fn try_theory() -> Result<Theory, SourceLoadError> {
    try_loaded().map(LoadedC::into_theory)
}

fn loaded_source() -> Result<&'static LoadedSource, SourceLoadError> {
    LOADED_C
        .get_or_init(load_c_source)
        .as_ref()
        .map_err(|error| error.clone())
}

fn loaded_computation_source() -> Result<&'static LoadedSource, SourceLoadError> {
    LOADED_C_COMPUTATIONS
        .get_or_init(load_c_computation_source)
        .as_ref()
        .map_err(|error| error.clone())
}

fn load_c_source() -> Result<LoadedSource, SourceLoadError> {
    let mut loaded = crate::prelude::try_loaded()?;

    for (section, source) in SOURCES {
        loaded.load_section(*section, source)?;
    }

    Ok(loaded)
}

fn load_c_computation_source() -> Result<LoadedSource, SourceLoadError> {
    let mut loaded =
        crate::prelude::try_loaded_computations().map_err(SourceLoadError::Computation)?;

    for (section, source) in SOURCES {
        loaded
            .load_computations_section(*section, source)
            .map_err(SourceLoadError::Computation)?;
    }

    Ok(loaded)
}

pub fn define_in_theory(theory: &mut Theory) -> bool {
    try_define_in_theory(theory).is_ok()
}

pub fn try_define_in_theory(theory: &mut Theory) -> Result<(), SourceLoadError> {
    crate::prelude::try_define_in_theory(theory)?;

    let loaded = loaded_source()?;
    let c_module_start = loaded
        .modules()
        .len()
        .checked_sub(SOURCES.len())
        .expect("loaded C model should include C source modules");

    for module in &loaded.modules()[c_module_start..] {
        define_module_computations_result_in_section(theory, module.parsed(), module.section())
            .map_err(SourceLoadError::Computation)?;
    }

    let pretty = loaded.source_env().pretty_env();
    for module in &loaded.modules()[c_module_start..] {
        define_module_theorems_result_in_section(
            theory,
            module.parsed(),
            module.section(),
            &pretty,
        )
        .map_err(SourceLoadError::Theorem)?;
    }

    Ok(())
}

pub fn define_theorems_in_theory(theory: &mut Theory) -> bool {
    try_define_theorems_in_theory(theory).is_ok()
}

pub fn try_define_theorems_in_theory(theory: &mut Theory) -> Result<(), SourceTheoremError> {
    let loaded = loaded_computation_source().map_err(|error| match error {
        SourceLoadError::ModuleParseFailed { section, error } => {
            SourceTheoremError::ModuleParseFailed { section, error }
        }
        SourceLoadError::Computation(error) => match error {
            SourceComputationError::ModuleParseFailed { section, error } => {
                SourceTheoremError::ModuleParseFailed { section, error }
            }
            SourceComputationError::ComputationRejected { .. } => {
                unreachable!("fresh C computation loading should not reject definitions")
            }
        },
        SourceLoadError::Theorem(_) => {
            unreachable!("computation-only C loading should not define theorems")
        }
    })?;
    let c_module_start = loaded
        .modules()
        .len()
        .checked_sub(SOURCES.len())
        .expect("loaded C model should include C source modules");

    let pretty = loaded.source_env().pretty_env();
    for module in &loaded.modules()[c_module_start..] {
        define_module_theorems_result_in_section(
            theory,
            module.parsed(),
            module.section(),
            &pretty,
        )?;
    }

    Ok(())
}

#[cfg(test)]
pub(crate) fn parsed_c_source_env() -> Result<&'static SourceEnv, SourceLoadError> {
    loaded_computation_source().map(LoadedSource::source_env)
}

#[cfg(test)]
pub(crate) fn parsed_c_modules() -> Result<Vec<&'static source::ParsedModule>, SourceLoadError> {
    loaded_computation_source().map(|loaded| {
        let modules = loaded.modules();

        modules
            .get(modules.len() - SOURCES.len()..)
            .expect("loaded C model should contain C modules")
            .iter()
            .map(LoadedModule::parsed)
            .collect()
    })
}

#[cfg(test)]
mod tests;
