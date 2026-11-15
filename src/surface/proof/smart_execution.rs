//! Smart execution search, fact transport, and theorem selection.

use super::proof_object::StepUntilTarget;
use super::*;
use std::collections::BTreeSet;

impl<'a> Proof<'a> {
    /// The refusal for a requirement an execution-frontier `apply` cannot
    /// discharge: the written clause, what its parameters were bound to, its
    /// instantiation spelled through the proof's names, and for a `viewable`
    /// which memory it reads, so a requirement over the current state never
    /// reads like the `at(iter, …)` fact beside it.
    fn describe_unavailable_execution_requirement(
        &self,
        theorem_environment: &TheoremEnvironment,
        application: &TheoremApplication,
        requirement_index: usize,
        requirement: &Proposition,
    ) -> String {
        let source = theorem_environment
            .get(&application.name)
            .and_then(|theorem| {
                let requirements =
                    crate::surface::proof::pure_theorems::theorem_requirement_propositions(theorem)
                        .ok()?;
                let written = requirements.get(requirement_index)?.clone();
                let bindings = theorem
                    .parameters()
                    .iter()
                    .zip(&application.arguments)
                    .map(|(parameter, argument)| {
                        (
                            parameter.name().to_string(),
                            crate::surface::diagnostics::describe_contract_expression(argument),
                        )
                    })
                    .collect::<Vec<_>>();
                Some((written, bindings))
            });
        // Spell the instantiation through the frontier's locals, so its
        // terms read as the names the reader wrote.
        let (parameters, arguments) = self.diagnostic_naming_tables();
        let instantiation = crate::surface::diagnostics::describe_stated_fact(
            requirement,
            ParameterBinding::new(&parameters, &arguments),
        );
        let message = match source {
            Some((written, bindings)) => {
                crate::surface::proof::theorem_application::describe_unavailable_theorem_requirement_spelled(
                    &application.name,
                    requirement_index,
                    &written,
                    &bindings,
                    &format!("`{instantiation}`"),
                )
            }
            None => format!(
                "theorem application `{}` requires an unavailable exact premise: {}",
                application.name,
                crate::surface::proof_diagnostics::render::render_proposition(requirement)
            ),
        };
        let writable = self
            .writable_theorem_requirement(application, requirement_index)
            .unwrap_or(instantiation);
        format!(
            "{message}{}{}",
            self.describe_viewable_memory_note(requirement),
            crate::surface::proof::theorem_application::requirement_search_miss(&writable)
        )
    }

    /// Requirement `requirement_index` of `application` as a proof writes it
    /// in a `have`: the theorem's `requires` with the written arguments
    /// substituted, which lowers to the fact the application looks up. The
    /// rendered instantiation can name evaluated pieces, such as `false` for
    /// `3u32 == 0u32`, that no `have` spells. `None` when it does not lower.
    pub(super) fn writable_theorem_requirement(
        &self,
        application: &TheoremApplication,
        requirement_index: usize,
    ) -> Option<String> {
        let (theorem, substitutions) = self.theorem_application_instance(application)?;
        let requirements =
            crate::surface::proof::pure_theorems::theorem_requirement_propositions(&theorem)
                .ok()?;
        let requirement = crate::surface::proof::theorem_application::observe_machine_parameters(
            requirements.get(requirement_index)?,
            theorem.parameters(),
            &substitutions,
        );
        let surface = substitute_click_proposition(&requirement, &substitutions).ok()?;
        self.lower_surface_proposition(&surface, "`apply` requirement")
            .ok()?;
        Some(crate::surface::printing::source_click_proposition(&surface))
    }

    /// For a missing `viewable` requirement, which memory it reads and which
    /// memory the available `viewable` facts of the same range read. The
    /// bounded renderer labels states per rendering, so without this a
    /// requirement over the current state and a fact at `at(iter, …)` print
    /// alike.
    fn describe_viewable_memory_note(&self, requirement: &Proposition) -> String {
        let Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        } = requirement
        else {
            return String::new();
        };
        let Some(execution) = self.execution() else {
            return String::new();
        };
        let name_memory = |candidate: &crate::kernel::Memory| {
            if candidate == execution.core.state.memory() {
                return "the current state".to_string();
            }
            execution
                .presentation
                .recorded_states
                .iter()
                .find(|(_, state)| state.memory() == candidate)
                .map(|(selector, _)| {
                    format!(
                        "`at({}, …)`",
                        crate::surface::diagnostics::describe_program_point_selector(selector)
                    )
                })
                .unwrap_or_else(|| "an earlier state no proof mark names".to_string())
        };
        let others = self
            .facts()
            .propositions()
            .filter_map(|fact| match fact {
                Proposition::MemoryLoadable {
                    memory: held,
                    base: held_base,
                    bytes: held_bytes,
                    wide: false,
                } if held_base == base && held_bytes == bytes && held != memory => {
                    Some(name_memory(held))
                }
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut note = format!(
            "\n  the required `viewable` reads the memory of {}",
            name_memory(memory)
        );
        if !others.is_empty() {
            note.push_str(&format!(
                "; the available `viewable` of the same range reads {}",
                others.into_iter().collect::<Vec<_>>().join(" and ")
            ));
        }
        note
    }

    /// Consult only the guard's indexed spellings and containing source facts.
    /// Re-lowering prevents a moved resource field or state name from citing
    /// an old fact under its current spelling.
    fn argument_guard_source(
        &self,
        guard: &Proposition,
    ) -> Option<(ClickProposition, Proposition)> {
        for forms in self
            .context_surface_propositions()
            .into_iter()
            .chain(std::iter::once(self.local_surface_facts()))
        {
            for whole in std::iter::once(guard).chain(forms.kernels_containing_conjunct(guard)) {
                for surface in forms.surfaces(whole) {
                    let Ok(lowered) =
                        self.lower_surface_proposition(surface, "argument evaluation guard")
                    else {
                        continue;
                    };
                    if lowered == *whole
                        && self.facts().listed_premise_available(&lowered, &[], false)
                    {
                        return Some((surface.clone(), lowered));
                    }
                }
            }
        }
        None
    }

    /// The guarantees of a theorem application as the caller would write
    /// them: each `ensures` of the applied theorem with the application's
    /// arguments substituted for its parameters, in declaration order.
    ///
    /// This spells conclusions; it establishes nothing. The caller retains
    /// one only after matching it against a fact the checked application
    /// added, so an application this cannot spell yields no conclusions
    /// rather than an error. A generic theorem is spelled only in a pure
    /// theorem proof, where its type instance is inferred from the
    /// arguments alone.
    pub(in crate::surface::proof) fn theorem_application_surface_conclusions(
        &self,
        application: &TheoremApplication,
    ) -> Vec<ClickProposition> {
        let Some((theorem, substitutions)) = self.theorem_application_instance(application) else {
            return Vec::new();
        };
        theorem
            .ensures()
            .iter()
            .filter_map(|ensure| match ensure.ensure() {
                Ensure::Proposition(conclusion) => substitute_click_proposition(
                    &crate::surface::proof::theorem_application::observe_machine_parameters(
                        conclusion,
                        theorem.parameters(),
                        &substitutions,
                    ),
                    &substitutions,
                )
                .ok(),
                _ => None,
            })
            .collect()
    }

    /// The theorem `application` names, instantiated, and its parameters'
    /// substitutions by the application's written arguments. A generic
    /// theorem is instantiated only in a pure theorem proof, where its type
    /// instance is inferred from the arguments alone.
    pub(super) fn theorem_application_instance(
        &self,
        application: &TheoremApplication,
    ) -> Option<(TheoremDefinition, BTreeMap<String, ContractExpression>)> {
        let written = application;
        let application = self.resolve_theorem_application(application).ok()?;
        let theorem_environment = match self.context.as_ref() {
            ProofContext::Pure(context) => context.theorem_environment,
            ProofContext::FixedState(context) => context.theorem_environment,
            ProofContext::Execution(context) => context.theorem_environment,
        };
        let theorem = theorem_environment.get(&application.name)?;
        let theorem = if theorem.type_parameters().is_empty() {
            theorem.clone()
        } else {
            let ProofContext::Pure(context) = self.context.as_ref() else {
                return None;
            };
            let state = ExecutionState::new().with_memory(context.theorem_context.memory.clone());
            let recorded_states = RecordedStates::new();
            let algebraic_values = application
                .arguments
                .iter()
                .flat_map(contract_expression_referenced_names)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .filter_map(|name| {
                    self.local_algebraic_values()
                        .get(&name)
                        .cloned()
                        .or_else(|| {
                            context
                                .structural_induction_setup
                                .as_ref()?
                                .algebraic_values
                                .get(&name)
                                .cloned()
                        })
                        .map(|value| (name, value))
                })
                .collect();
            let application_context = TheoremApplicationContext {
                values: &context.theorem_context.values,
                array_refs: &context.theorem_context.array_refs,
                algebraic_values: &algebraic_values,
                pre_state: &state,
                post_state: &state,
                result: None,
                recorded_states: &recorded_states,
                integer_values: &context.theorem_context.integer_values,
                pointer_element_widths: BTreeMap::new(),
            };
            let Ok(theorem) = instantiate_generic_theorem_application_definition(
                theorem,
                &application,
                self.facts().assumptions(),
                &application_context,
                context.spec_definitions,
            ) else {
                return None;
            };
            theorem
        };
        if theorem.parameters().len() != application.arguments.len() {
            return None;
        }
        // The written arguments, not the resolved ones: resolution replaces
        // a `match` arm's C binding by its kernel value, which has no
        // spelling.
        let substitutions = theorem
            .parameters()
            .iter()
            .map(FunctionParameter::name)
            .map(str::to_string)
            .zip(written.arguments.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        Some((theorem, substitutions))
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/proof/smart_execution.rs");
}

// Discovery methods are deliberately not methods of Proof.

// Source spelling adapters for the kernel ProofSearch interface.
mod history_equalities;
mod search;

#[path = "driver/theorems.rs"]
mod driver;
