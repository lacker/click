//! Selected source queries; enumeration carries exact premises, not new authority.
use super::*;
use crate::kernel::assumptions::load_state_and_pointer;
use crate::kernel::assumptions::{parameter_alias_bucket, parameter_partition_variable};
use crate::kernel::reasoning::memories_match_for_pointer_load;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{ConditionTerm, Proposition};
use std::collections::BTreeSet;

impl EqualityGraph {
    pub(in crate::kernel) fn offsets_with_an_alias_at_root(
        &self,
        root: &Option<PointerOffsetTerm>,
    ) -> Vec<PointerOffsetTerm> {
        self.admitted
            .pointer_offset_aliases_by_root
            .get(root)
            .into_iter()
            .flat_map(|pairs| pairs.iter())
            .map(|(aliased, _)| {
                crate::instrumentation::record_deterministic_work(1);
                aliased.clone()
            })
            .collect()
    }

    pub(in crate::kernel) fn has_pointer_block_aliases(&self) -> bool {
        !self.admitted.pointer_block_aliases.is_empty()
    }

    pub(in crate::kernel) fn exact_pointer_offset_aliases(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = Pointer> + '_ {
        let block = pointer.block.clone();
        self.admitted
            .pointer_offset_aliases
            .get(&pointer.offset)
            .into_iter()
            .flat_map(|aliases| aliases.iter())
            .map(move |offset| Pointer {
                block: block.clone(),
                offset: offset.clone(),
            })
    }

    pub(in crate::kernel) fn exact_pointer_offset_alias_count(&self, pointer: &Pointer) -> usize {
        self.admitted
            .pointer_offset_aliases
            .get(&pointer.offset)
            .map_or(0, |aliases| aliases.len())
    }

    pub(in crate::kernel) fn exactly_aliased_pointers(
        &self,
    ) -> impl ExactSizeIterator<Item = &Pointer> {
        self.admitted.pointer_block_aliases.keys()
    }

    /// A unique directly stated alias, selected by cached bucket length.
    /// Multiple alternatives belong to premise search, not checked lookup.
    pub(in crate::kernel) fn unique_exact_pointer_alias(
        &self,
        pointer: &Pointer,
    ) -> Option<&Pointer> {
        let aliases = self.admitted.pointer_block_aliases.get(pointer)?;
        if aliases.len() != 1 {
            return None;
        }
        aliases.iter().next().map(|(alias, _)| alias)
    }

    pub(in crate::kernel) fn exact_pointer_aliases(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = &Pointer> {
        self.admitted
            .pointer_block_aliases
            .get(pointer)
            .into_iter()
            .flat_map(|aliases| aliases.iter().map(|(alias, _)| alias))
    }

    pub(in crate::kernel) fn exact_uint64_equalities(
        &self,
        term: &MachineTerm,
    ) -> impl Iterator<Item = (&MachineTerm, &ConditionTerm)> {
        self.exact_uint64_equalities_view(crate::kernel::MachineOperandView::Legacy(term))
    }

    pub(in crate::kernel) fn exact_uint64_equalities_view(
        &self,
        term: crate::kernel::MachineOperandView<'_>,
    ) -> impl Iterator<Item = (&MachineTerm, &ConditionTerm)> {
        self.admitted
            .bitvector64_equality_facts
            .get(
                &crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::for_format(
                    MachineIntegerType::UInt64,
                    term,
                ),
            )
            .into_iter()
            .flat_map(|neighbors| neighbors.iter())
    }

    pub(in crate::kernel) fn algebraic_constructor_field_sources(
        &self,
        field: &Proposition,
    ) -> impl Iterator<Item = &(Proposition, usize)> {
        self.admitted
            .algebraic_constructor_field_equalities
            .get(field)
            .into_iter()
            .flat_map(|sources| sources.iter().map(|(source, ())| source))
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn recorded_uint64_equals(
        &self,
        term: &MachineTerm,
    ) -> Vec<(MachineTerm, ConditionTerm)> {
        let exact = self
            .admitted
            .bitvector64_equality_facts
            .get(
                &crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::for_format(
                    MachineIntegerType::UInt64,
                    crate::kernel::MachineOperandView::Legacy(term),
                ),
            )
            .map(|neighbors| {
                neighbors
                    .iter()
                    .map(|(equal, fact)| (equal.clone(), fact.clone()))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        if !exact.is_empty() {
            return exact;
        }
        let Some((query_memory, pointer, kind)) = load_state_and_pointer(term) else {
            return exact;
        };
        let mut transported = Vec::new();
        let candidates = self
            .admitted
            .wide_load_sources
            .get(&(pointer.clone(), kind));
        for condition in candidates.into_iter().flat_map(|sources| sources.iter()) {
            crate::instrumentation::record_deterministic_work(1);
            let ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } = condition
            else {
                continue;
            };
            for (side, other) in [(left, right), (right, left)] {
                let Some((fact_memory, fact_pointer, fact_kind)) = load_state_and_pointer(side)
                else {
                    continue;
                };
                if fact_pointer != pointer
                    || fact_kind != kind
                    || !memories_match_for_pointer_load(&fact_memory, &query_memory, &pointer)
                {
                    continue;
                }
                transported.push((other.as_ref().clone(), condition.clone()));
            }
        }
        transported
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn exact_literal_sources(
        &self,
        term: &MachineTerm,
    ) -> Option<&crate::persistent::PersistentMap<ConditionTerm, i64>> {
        self.exact_literal_sources_view(crate::kernel::MachineOperandView::Legacy(term))
    }

    pub(in crate::kernel) fn exact_literal_sources_view(
        &self,
        term: crate::kernel::MachineOperandView<'_>,
    ) -> Option<&crate::persistent::PersistentMap<ConditionTerm, i64>> {
        self.admitted
            .exact_constant_equalities
            .get(&crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::new(term))
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn parameter_store_alias_bases(
        &self,
        base: &Pointer,
    ) -> Option<BTreeSet<Pointer>> {
        let mut pending = vec![base.clone()];
        let mut seen = BTreeSet::new();
        let mut bases = BTreeSet::new();
        let mut visited_terms = BTreeSet::new();
        while let Some(pointer) = pending.pop() {
            let pointer = parameter_alias_bucket(&pointer);
            if !seen.insert(pointer.clone()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(variable) = parameter_partition_variable(&pointer) {
                if self.admitted.bitvector64_equality_facts.contains_key(
                    &crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::for_format(
                        MachineIntegerType::UInt64,
                        crate::kernel::MachineOperandView::Legacy(&MachineTerm::Variable(
                            *variable,
                        )),
                    ),
                ) {
                    return None;
                }
                bases.insert(pointer.clone());
            }
            let mut terms: Vec<_> = self
                .admitted
                .wide_pointer_alias_endpoints_by_object
                .get(&pointer)
                .into_iter()
                .flat_map(|endpoints| endpoints.iter().cloned())
                .collect();
            while let Some(term) = terms.pop() {
                if !visited_terms.insert(term.clone()) {
                    continue;
                }
                crate::instrumentation::record_deterministic_work(1);
                if let Some(address) = term.address_pointer() {
                    pending.push(address.clone());
                }
                if let Some(neighbors) = self.admitted.bitvector64_equality_facts.get(
                    &crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::for_format(
                        MachineIntegerType::UInt64,
                        crate::kernel::MachineOperandView::Legacy(&term),
                    ),
                ) {
                    terms.extend(neighbors.keys().cloned());
                }
            }
            if let Some(endpoints) = self
                .admitted
                .pointer_alias_endpoints_by_object
                .get(&pointer)
            {
                for endpoint in endpoints.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    if let Some(aliases) = self.admitted.pointer_block_aliases.get(endpoint) {
                        pending.extend(aliases.keys().cloned());
                    }
                }
            }
        }
        Some(bases)
    }

    pub(in crate::kernel) fn address_connected_objects(
        &self,
        pointer: &Pointer,
    ) -> BTreeSet<Pointer> {
        let mut reached_objects = BTreeSet::new();
        if self
            .admitted
            .wide_pointer_alias_endpoints_by_object
            .is_empty()
        {
            return reached_objects;
        }
        let mut pending = vec![parameter_alias_bucket(pointer)];
        let mut seen = BTreeSet::new();
        let mut visited_terms = BTreeSet::new();
        while let Some(bucket) = pending.pop() {
            if !seen.insert(bucket.clone()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let mut terms: Vec<_> = self
                .admitted
                .wide_pointer_alias_endpoints_by_object
                .get(&bucket)
                .into_iter()
                .flat_map(|endpoints| endpoints.iter().cloned())
                .collect();
            while let Some(term) = terms.pop() {
                if !visited_terms.insert(term.clone()) {
                    continue;
                }
                crate::instrumentation::record_deterministic_work(1);
                if let Some(address) = term.address_pointer() {
                    let reached = parameter_alias_bucket(address);
                    reached_objects.insert(reached.clone());
                    pending.push(reached);
                }
                if let Some(neighbors) = self.admitted.bitvector64_equality_facts.get(
                    &crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey::for_format(
                        MachineIntegerType::UInt64,
                        crate::kernel::MachineOperandView::Legacy(&term),
                    ),
                ) {
                    terms.extend(neighbors.keys().cloned());
                }
            }
        }
        reached_objects
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn reset_closure(&mut self) {
        let sources = {
            let state = self.state.lock().expect("equality graph");
            (
                state.pointer_fact_inputs.clone(),
                state.condition_pointer_fact_inputs.clone(),
            )
        };
        let admitted = std::mem::take(&mut self.admitted);
        *self = Self::default();
        self.admitted = admitted;
        for (_, source) in sources.0.iter().chain(sources.1.iter()) {
            self.adjust_pointer_fact_source(source, true);
        }
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn identity_only(&self) -> Self {
        let mut identity = Self::default();
        identity.admitted.typed_pointer_read_definitions =
            self.admitted.typed_pointer_read_definitions.clone();
        identity
    }
}

impl EqualityGraph {
    pub(in crate::kernel) fn has_wide_pointer_sources(&self) -> bool {
        !self
            .admitted
            .wide_pointer_alias_endpoints_by_object
            .is_empty()
    }
}
