//! Definition-level restrictions on direct worker transfer.
//!
//! An authority control owns a population authority, and moving the control
//! alone does not transfer the authority's loans or mutex custody. Until a
//! synchronization protocol owns it, the control stays in its creating
//! thread, as a mutex authority does. A resource containing such a control
//! inherits the restriction. This property is computed once when definitions are
//! installed; a worker handoff only reads it.

use std::collections::{BTreeMap, VecDeque};

use super::{CompositeResourceDefinition, Resource, ResourceFact};

pub(super) fn propagate_thread_confinement(definitions: &mut [CompositeResourceDefinition]) {
    for definition in definitions.iter_mut() {
        definition.contains_mutex_authority = definition
            .contains
            .iter()
            .chain(
                definition
                    .matched
                    .iter()
                    .flat_map(|body| body.arms.iter())
                    .flat_map(|arm| arm.contains.iter()),
            )
            .any(|spec| {
                matches!(
                    spec.family(),
                    super::ResourceFamily::MutexGuard
                        | super::ResourceFamily::MutexLive
                        | super::ResourceFamily::MutexUse
                )
            });
        definition.thread_confined |= definition.contains_mutex_authority;
    }
    let dependents = definition_dependents(definitions);
    propagate_population_reach_with(definitions, &dependents);
    let mut pending: VecDeque<_> = definitions
        .iter()
        .enumerate()
        .filter_map(|(index, definition)| definition.thread_confined.then_some(index))
        .collect();
    while let Some(child) = pending.pop_front() {
        for &parent in &dependents[child] {
            if !definitions[parent].thread_confined
                || (definitions[child].contains_mutex_authority
                    && !definitions[parent].contains_mutex_authority)
            {
                definitions[parent].thread_confined = true;
                definitions[parent].contains_mutex_authority |=
                    definitions[child].contains_mutex_authority;
                pending.push_back(parent);
            }
        }
    }
}

/// Marks each definition that is authorized, holds a population authority,
/// or contains or names such a definition. The surface's own definition list
/// and the kernel-installed one must agree, so both run this pass.
pub(crate) fn propagate_population_reach(definitions: &mut [CompositeResourceDefinition]) {
    let dependents = definition_dependents(definitions);
    propagate_population_reach_with(definitions, &dependents);
}

fn propagate_population_reach_with(
    definitions: &mut [CompositeResourceDefinition],
    dependents: &[Vec<usize>],
) {
    for definition in definitions.iter_mut() {
        definition.reaches_population = definition.authorized
            || definition
                .contains
                .iter()
                .chain(
                    definition
                        .matched
                        .iter()
                        .flat_map(|body| body.arms.iter())
                        .flat_map(|arm| arm.contains.iter()),
                )
                .any(|spec| matches!(spec.term(), super::ResourceTerm::PopulationAuthority { .. }));
    }
    let mut reaching: VecDeque<_> = definitions
        .iter()
        .enumerate()
        .filter_map(|(index, definition)| definition.reaches_population.then_some(index))
        .collect();
    while let Some(child) = reaching.pop_front() {
        for &parent in &dependents[child] {
            if !definitions[parent].reaches_population {
                definitions[parent].reaches_population = true;
                reaching.push_back(parent);
            }
        }
    }
}

/// For each definition, the definitions that contain or name it as a child.
fn definition_dependents(definitions: &[CompositeResourceDefinition]) -> Vec<Vec<usize>> {
    let by_name: BTreeMap<&str, usize> = definitions
        .iter()
        .enumerate()
        .map(|(index, definition)| (definition.name(), index))
        .collect();
    let mut dependents = vec![Vec::new(); definitions.len()];
    for (parent, definition) in definitions.iter().enumerate() {
        let contained = definition
            .contains
            .iter()
            .chain(
                definition
                    .matched
                    .iter()
                    .flat_map(|body| body.arms.iter())
                    .flat_map(|arm| arm.contains.iter()),
            )
            .filter_map(|spec| spec.contained_definition_name());
        let children = definition.children.iter().chain(
            definition
                .matched
                .iter()
                .flat_map(|body| body.arms.iter())
                .flat_map(|arm| arm.children.iter()),
        );
        for name in contained.chain(children.map(|child| child.resource.as_str())) {
            if let Some(&child) = by_name.get(name) {
                dependents[child].push(parent);
            }
        }
    }
    dependents
}

pub(super) fn confined_resource_name<'a>(
    fact: &'a ResourceFact,
    definitions: &[CompositeResourceDefinition],
) -> Option<&'a str> {
    let name = match fact {
        ResourceFact::Own(
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
            _,
        )
        | ResourceFact::View(
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
        ) => return None,
        // Moving the atom alone does not transfer its loan share/hold custody.
        ResourceFact::Own(Resource::PopulationAuthority(description), _)
        | ResourceFact::View(Resource::PopulationAuthority(description)) => {
            return Some(description.family());
        }
        ResourceFact::Own(Resource::MutexUse(_), _) | ResourceFact::View(Resource::MutexUse(_)) => {
            return Some("mutex use");
        }
        ResourceFact::Own(Resource::MutexLive(_), _)
        | ResourceFact::View(Resource::MutexLive(_)) => return Some("mutex lifetime"),
        ResourceFact::Own(Resource::MutexGuard(_), _)
        | ResourceFact::View(Resource::MutexGuard(_)) => return Some("mutex guard"),
        ResourceFact::Own(Resource::Composite { name, .. }, _)
        | ResourceFact::View(Resource::Composite { name, .. })
        | ResourceFact::Own(Resource::Token { name, .. }, _)
        | ResourceFact::View(Resource::Token { name, .. }) => name.as_str(),
        ResourceFact::Own(Resource::Instance(instance), _)
        | ResourceFact::View(Resource::Instance(instance)) => instance.name.as_str(),
        // A publication right is the handoff itself: a worker may hold it.
        ResourceFact::Own(
            Resource::Memory(_) | Resource::Iterated(_) | Resource::Publication(_),
            _,
        )
        | ResourceFact::View(
            Resource::Memory(_) | Resource::Iterated(_) | Resource::Publication(_),
        ) => {
            return None;
        }
    };
    definitions
        .binary_search_by(|definition| definition.name().cmp(name))
        .ok()
        .filter(|&index| definitions[index].thread_confined)
        .map(|_| name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{ResourceAccessMode, ResourceSpec, SpecProposition};

    #[test]
    fn a_bodyless_member_can_move_but_an_authority_control_is_confined() {
        let member =
            CompositeResourceDefinition::new("member", vec![], None, false, vec![], vec![])
                .with_authorized(true);
        let control = CompositeResourceDefinition::authority_control(
            "control",
            vec![],
            None,
            vec![],
            vec![SpecProposition::Predicate {
                resource_state_dependent: true,
                name: "population_invariant".into(),
                arguments: vec![],
            }],
        );
        let mut definitions = vec![member, control];
        propagate_thread_confinement(&mut definitions);
        assert!(!definitions[0].is_thread_confined());
        assert!(definitions[1].is_thread_confined());
    }

    #[test]
    fn guard_ingredient_confines_its_transitive_wrappers() {
        use crate::kernel::{
            Pointer, ProgramExpression, ProgramValue, ResourceQuantity, ResourceStateSource,
            ResourceTerm, ResourceTransferRole,
        };
        let guard = ResourceSpec::new(
            ResourceTerm::MutexGuard {
                mutex: Box::new(ProgramExpression::Value(ProgramValue::pointer(
                    Pointer::null(),
                ))),
                state_source: ResourceStateSource::Current,
            },
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            ResourceTransferRole::Consume,
            ResourceStateSource::Current,
        )
        .unwrap();
        let inner =
            CompositeResourceDefinition::new("inner", vec![], None, false, vec![guard], vec![]);
        let outer = CompositeResourceDefinition::new(
            "outer",
            vec![],
            None,
            false,
            vec![ResourceSpec::composite(
                ResourceAccessMode::Own,
                "inner".into(),
                vec![],
                vec![],
            )],
            vec![],
        );
        let mut definitions = vec![inner, outer];
        propagate_thread_confinement(&mut definitions);
        assert!(
            definitions
                .iter()
                .all(CompositeResourceDefinition::is_thread_confined)
        );
        assert_eq!(
            confined_resource_name(
                &ResourceFact::own_composite("outer".into(), vec![]),
                &definitions
            ),
            Some("outer")
        );
    }

    #[test]
    fn containing_a_confined_resource_inherits_confinement() {
        let contained =
            ResourceSpec::composite(ResourceAccessMode::Own, "reference".into(), vec![], vec![]);
        let outer = CompositeResourceDefinition::new(
            "wrapper",
            vec![],
            None,
            false,
            vec![contained],
            vec![],
        );
        let inner = CompositeResourceDefinition::authority_control(
            "reference",
            vec![],
            None,
            vec![],
            vec![SpecProposition::Predicate {
                resource_state_dependent: true,
                name: "population_invariant".into(),
                arguments: vec![],
            }],
        );
        let mut definitions = vec![inner, outer];
        propagate_thread_confinement(&mut definitions);
        assert!(definitions[1].is_thread_confined());
        let wrapped = ResourceFact::view_composite("wrapper".into(), vec![]);
        assert_eq!(
            confined_resource_name(&wrapped, &definitions),
            Some("wrapper")
        );
    }
}
