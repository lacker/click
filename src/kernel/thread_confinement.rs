//! Definition-level restrictions on direct worker transfer.
//!
//! A counted population with a body can expose one shared invariant through
//! several units. Until a synchronization protocol owns that body, its units
//! stay in their creating thread. A resource containing such a unit inherits
//! the restriction. This property is computed once when definitions are
//! installed; a worker handoff only reads it.

use std::collections::{BTreeMap, VecDeque};

use super::{CCompositeResourceDefinition, CResource, CResourceFact};

pub(super) fn propagate_thread_confinement(definitions: &mut [CCompositeResourceDefinition]) {
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
    let mut pending: VecDeque<_> = definitions
        .iter()
        .enumerate()
        .filter_map(|(index, definition)| definition.thread_confined.then_some(index))
        .collect();
    while let Some(child) = pending.pop_front() {
        for &parent in &dependents[child] {
            if !definitions[parent].thread_confined {
                definitions[parent].thread_confined = true;
                pending.push_back(parent);
            }
        }
    }
}

pub(super) fn confined_resource_name<'a>(
    fact: &'a CResourceFact,
    definitions: &[CCompositeResourceDefinition],
) -> Option<&'a str> {
    let name = match fact {
        CResourceFact::Own(CResource::MutexGuard(_), _)
        | CResourceFact::View(CResource::MutexGuard(_)) => return Some("mutex guard"),
        CResourceFact::Own(CResource::Composite { name, .. }, _)
        | CResourceFact::View(CResource::Composite { name, .. })
        | CResourceFact::Own(CResource::Token { name, .. }, _)
        | CResourceFact::View(CResource::Token { name, .. }) => name.as_str(),
        CResourceFact::Own(CResource::Instance(instance), _)
        | CResourceFact::View(CResource::Instance(instance)) => instance.name.as_str(),
        CResourceFact::Own(CResource::Memory(_) | CResource::Iterated(_), _)
        | CResourceFact::View(CResource::Memory(_) | CResource::Iterated(_)) => {
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
    use crate::kernel::{CResourceAccessMode, CResourceSpec, SpecProposition};

    #[test]
    fn bodyless_counted_resource_can_move_but_stateful_population_is_confined() {
        let bodyless = CCompositeResourceDefinition::counted_population(
            "ticket",
            vec![],
            None,
            vec![],
            vec![],
        );
        let stateful = CCompositeResourceDefinition::counted_population(
            "reference",
            vec![],
            None,
            vec![],
            vec![SpecProposition::Predicate {
                name: "population_invariant".into(),
                arguments: vec![],
            }],
        );
        assert!(!bodyless.is_thread_confined());
        assert!(stateful.is_thread_confined());
    }

    #[test]
    fn containing_a_confined_resource_inherits_confinement() {
        let contained =
            CResourceSpec::composite(CResourceAccessMode::Own, "reference".into(), vec![], vec![]);
        let outer = CCompositeResourceDefinition::new(
            "wrapper",
            vec![],
            None,
            false,
            vec![contained],
            vec![],
        );
        let inner = CCompositeResourceDefinition::counted_population(
            "reference",
            vec![],
            None,
            vec![],
            vec![SpecProposition::Predicate {
                name: "population_invariant".into(),
                arguments: vec![],
            }],
        );
        let mut definitions = vec![inner, outer];
        propagate_thread_confinement(&mut definitions);
        assert!(definitions[1].is_thread_confined());
        let wrapped = CResourceFact::view_composite("wrapper".into(), vec![]);
        assert_eq!(
            confined_resource_name(&wrapped, &definitions),
            Some("wrapper")
        );
    }
}
