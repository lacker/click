//! Which resource definitions own memory no clause instance names.
//!
//! A held resource's owned footprint is derived from its definitions
//! (`OwnedFootprintDerivation` in `functions.rs`): each owned clause of each
//! body, with the parameters bound to the arguments, and the same for every
//! contained family and named child. That descent follows definitions, so it
//! is finite exactly when no definition can reach itself. A definition on a
//! cycle -- a recursive family, directly or through another -- owns one set
//! of clause instances per node, however many nodes are live, and an
//! instance body that binds an existential witness owns memory at an address
//! no argument spells. Either owns memory the derivation cannot name, and so
//! does every definition that contains or names one as a child. This is
//! decided once, when the definitions are installed, in time linear in the
//! definitions and the family references between them; a footprint
//! derivation only reads the flag.

use std::collections::{BTreeMap, VecDeque};

use super::CCompositeResourceDefinition;

pub(super) fn propagate_owned_footprint_reach(definitions: &mut [CCompositeResourceDefinition]) {
    let by_name: BTreeMap<&str, usize> = definitions
        .iter()
        .enumerate()
        .map(|(index, definition)| (definition.name(), index))
        .collect();
    let mut references = vec![Vec::new(); definitions.len()];
    let mut unnamed = vec![false; definitions.len()];
    for (parent, definition) in definitions.iter().enumerate() {
        unnamed[parent] = definition.is_recursive()
            || (definition.instance_schema.is_some() && !definition.witnesses.is_empty());
        // A name this set does not define is a token family, which owns no
        // bytes; a composite or instance fact of an undefined family is
        // refused where the derivation meets it.
        for name in definition.referenced_family_names() {
            if let Some(&child) = by_name.get(name) {
                references[parent].push(child);
            }
        }
    }
    for component in strongly_connected_components(&references) {
        if component.len() > 1 {
            for index in component {
                unnamed[index] = true;
            }
        }
    }
    for (index, children) in references.iter().enumerate() {
        if children.contains(&index) {
            unnamed[index] = true;
        }
    }
    let mut dependents = vec![Vec::new(); definitions.len()];
    for (parent, children) in references.iter().enumerate() {
        for &child in children {
            dependents[child].push(parent);
        }
    }
    let mut pending: VecDeque<usize> = (0..definitions.len())
        .filter(|&index| unnamed[index])
        .collect();
    while let Some(child) = pending.pop_front() {
        for &parent in &dependents[child] {
            if !unnamed[parent] {
                unnamed[parent] = true;
                pending.push_back(parent);
            }
        }
    }
    crate::instrumentation::record_deterministic_work(
        definitions.len() + references.iter().map(Vec::len).sum::<usize>(),
    );
    for (definition, unnamed) in definitions.iter_mut().zip(unnamed) {
        definition.owned_footprint_unnamed = unnamed;
    }
}

/// Kosaraju's two passes, iteratively: each node and edge is visited twice.
fn strongly_connected_components(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let count = edges.len();
    let mut order = Vec::with_capacity(count);
    let mut visited = vec![false; count];
    for root in 0..count {
        if visited[root] {
            continue;
        }
        visited[root] = true;
        let mut stack = vec![(root, 0usize)];
        while let Some((node, next)) = stack.last_mut() {
            if let Some(&child) = edges[*node].get(*next) {
                *next += 1;
                if !visited[child] {
                    visited[child] = true;
                    stack.push((child, 0));
                }
            } else {
                order.push(*node);
                stack.pop();
            }
        }
    }
    let mut reversed = vec![Vec::new(); count];
    for (node, children) in edges.iter().enumerate() {
        for &child in children {
            reversed[child].push(node);
        }
    }
    let mut assigned = vec![false; count];
    let mut components = Vec::new();
    for &root in order.iter().rev() {
        if assigned[root] {
            continue;
        }
        assigned[root] = true;
        let mut component = Vec::new();
        let mut stack = vec![root];
        while let Some(node) = stack.pop() {
            component.push(node);
            for &parent in &reversed[node] {
                if !assigned[parent] {
                    assigned[parent] = true;
                    stack.push(parent);
                }
            }
        }
        components.push(component);
    }
    components
}
