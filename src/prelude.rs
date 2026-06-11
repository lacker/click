//! Standard definitions layered on top of the kernel.

mod list;
#[cfg(test)]
mod list_tests;
mod nat;
#[cfg(test)]
mod nat_tests;
#[cfg(test)]
mod prelude_tests;

use std::sync::OnceLock;

use crate::{
    Name, Symbol, Theory,
    elab::{
        LoadedSource, SourceEnv,
        loader::{
            define_module_computations_result_in_section, define_module_theorems_result_in_section,
        },
    },
};

#[cfg(test)]
use crate::elab::{
    loader::{LoadedModule, define_module_computations_result, define_module_theorems_result},
    source,
};

pub use crate::elab::{
    ParseError, ProofElaborationError, SourceComputationError, SourceFileLoadError,
    SourceLoadError, SourceSection, SourceTheoremError,
};

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

    define_modules_in_theory_result(theory, loaded)
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

#[cfg(test)]
pub(crate) fn parsed_prelude_source_env() -> Result<&'static SourceEnv, SourceComputationError> {
    loaded_computation_source().map(LoadedSource::source_env)
}

#[cfg(test)]
pub(crate) fn parsed_list_modules()
-> Result<Vec<&'static source::ParsedModule>, SourceComputationError> {
    loaded_computation_source().map(|loaded| {
        let modules = loaded.modules();

        modules
            .get(..list::SOURCES.len())
            .expect("prelude should contain list modules")
            .iter()
            .map(LoadedModule::parsed)
            .collect()
    })
}

#[cfg(test)]
pub(crate) fn parsed_nat_modules()
-> Result<Vec<&'static source::ParsedModule>, SourceComputationError> {
    loaded_computation_source().map(|loaded| {
        let modules = loaded.modules();

        modules
            .get(list::SOURCES.len()..)
            .expect("prelude should contain nat modules")
            .iter()
            .map(LoadedModule::parsed)
            .collect()
    })
}

fn load_prelude_source() -> Result<LoadedSource, SourceLoadError> {
    let mut loaded = LoadedSource::with_source_env(prelude_source_env());

    for (section, source) in list::SOURCES {
        loaded.load_section(*section, source)?;
    }

    for (section, source) in nat::SOURCES {
        loaded.load_section(*section, source)?;
    }

    Ok(loaded)
}

fn load_prelude_computation_source() -> Result<LoadedSource, SourceComputationError> {
    let mut loaded = LoadedSource::with_source_env(prelude_source_env());

    for (section, source) in list::SOURCES {
        loaded.load_computations_section(*section, source)?;
    }

    for (section, source) in nat::SOURCES {
        loaded.load_computations_section(*section, source)?;
    }

    Ok(loaded)
}

pub(crate) fn prelude_source_env() -> SourceEnv {
    let mut env = SourceEnv::new();

    env.intern_symbol("unit");

    env
}

fn define_modules_in_theory_result(
    theory: &mut Theory,
    loaded: &LoadedSource,
) -> Result<(), SourceLoadError> {
    for module in loaded.modules() {
        define_module_computations_result_in_section(theory, module.parsed(), module.section())
            .map_err(SourceLoadError::Computation)?;
    }

    let pretty = loaded.source_env().pretty_env();
    for module in loaded.modules() {
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

#[cfg(test)]
fn define_module_in_theory_result(
    theory: &mut Theory,
    module: &source::ParsedModule,
) -> Result<(), SourceLoadError> {
    define_module_computations_result(theory, module).map_err(SourceLoadError::Computation)?;
    define_module_theorems_result(theory, module).map_err(SourceLoadError::Theorem)?;

    Ok(())
}

pub fn define_computations_in_theory(theory: &mut Theory) -> bool {
    try_define_computations_in_theory(theory).is_ok()
}

pub fn try_define_computations_in_theory(
    theory: &mut Theory,
) -> Result<(), SourceComputationError> {
    let loaded = loaded_computation_source()?;

    for module in loaded.modules() {
        define_module_computations_result_in_section(theory, module.parsed(), module.section())?;
    }

    Ok(())
}

pub fn define_theorems_in_theory(theory: &mut Theory) -> bool {
    try_define_theorems_in_theory(theory).is_ok()
}

pub fn try_define_theorems_in_theory(theory: &mut Theory) -> Result<(), SourceTheoremError> {
    let loaded = loaded_computation_source().map_err(|error| match error {
        SourceComputationError::ModuleParseFailed { section, error } => {
            SourceTheoremError::ModuleParseFailed { section, error }
        }
        SourceComputationError::ComputationRejected { .. } => {
            unreachable!("fresh prelude computation loading should not reject definitions")
        }
    })?;

    let pretty = loaded.source_env().pretty_env();
    for module in loaded.modules() {
        define_module_theorems_result_in_section(
            theory,
            module.parsed(),
            module.section(),
            &pretty,
        )?;
    }

    Ok(())
}
