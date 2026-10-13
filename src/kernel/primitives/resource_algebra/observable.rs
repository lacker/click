use super::*;

impl ResourceContext {
    /// Derived storage carries no cached decisions. Each returned composition
    /// consults its caller's current loan bindings and checked assumptions.
    fn composition_from_storage(&self, storage: std::sync::Arc<ResourceContextStorage>) -> Self {
        let pairings = if std::sync::Arc::ptr_eq(&storage, &self.storage) {
            self.memory_equalities
                .lock()
                .expect("memory equality index")
                .clone()
        } else {
            Default::default()
        };
        Self {
            instance_consumptions: self.instance_consumptions.clone(),
            memory_equalities: std::sync::Mutex::new(pairings),
            observable_projection: Default::default(),
            storage,
            loan_dependencies: self.loan_dependencies.clone(),
        }
    }

    pub(in crate::kernel) fn observable_composition(&self) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let classification = super::super::memory_state::never_address_taken_generation();
        let mut cache = self
            .observable_projection
            .lock()
            .expect("observable resource projection");
        if let Some(view) = cache.as_ref()
            && view.classification == classification
            && view.source.as_ptr() == std::sync::Arc::as_ptr(&self.storage)
        {
            return self.composition_from_storage(view.storage.clone());
        }
        let mut composition = self.observable_composition_uncached();
        self.retain_observable_source(&mut composition);
        *cache = Some(ObservableResourceProjection {
            classification,
            source: std::sync::Arc::downgrade(&self.storage),
            storage: composition.storage.clone(),
        });
        composition
    }

    /// Keep upstream's admission provenance for a filtered observation. An
    /// ignored private delta retains its existing storage and checkpoint;
    /// changed visible facts receive the current unfiltered source.
    fn retain_observable_source(&self, composition: &mut Self) {
        if !std::sync::Arc::ptr_eq(&composition.storage, &self.storage) {
            std::sync::Arc::make_mut(&mut composition.storage).observable_projection_source =
                Some((
                    crate::kernel::primitives::never_address_taken_locals_key(),
                    self.storage.clone(),
                ));
        }
    }

    /// The previous projection is retained as a compatibility reference for
    /// tests and as the cold path after an addressability change or a whole-
    /// input resource rewrite. Filtered storage never inherits raw pairings.
    pub(in crate::kernel) fn observable_composition_uncached(&self) -> Self {
        let mut composition = self.composition_from_storage(self.storage.clone());
        for (block, entries) in self.storage.index.owned_automatic_memory_by_block.iter() {
            crate::instrumentation::record_deterministic_work(1);
            if crate::kernel::block_is_never_address_taken_local(block) {
                for entry in entries.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    composition.remove_entry(*entry);
                }
            }
        }
        composition
    }

    /// Updating the view at the producer bounds its pending work: forks share
    /// the old view, and an unchanged private frame retains the exact root.
    /// The weak source checkpoint also refuses an unhandled storage change.
    ///
    /// `private_delta` says the producer's change is hidden from every
    /// observation. While nothing is filtered the view is the source root
    /// itself; the delta then either keeps that root or adopts the new
    /// source, without mirroring the change into a second copy of storage.
    fn advance_observable_projection(
        &mut self,
        previous: &std::sync::Arc<ResourceContextStorage>,
        private_delta: bool,
        update: impl FnOnce(&Self, &mut Self),
    ) {
        let cache = if let Some(cache) = std::sync::Arc::get_mut(&mut self.observable_projection) {
            cache
                .get_mut()
                .expect("observable resource projection")
                .take()
        } else {
            let retained = self
                .observable_projection
                .lock()
                .expect("observable resource projection")
                .clone();
            // Existing immutable forks must keep their own cold/warm view.
            self.observable_projection = Default::default();
            retained
        };
        let Some(view) = cache else {
            return;
        };
        let classification = super::super::memory_state::never_address_taken_generation();
        if view.classification != classification
            || view.source.as_ptr() != std::sync::Arc::as_ptr(previous)
        {
            return;
        }
        crate::instrumentation::record_deterministic_work(1);
        let storage = if std::sync::Arc::ptr_eq(&view.storage, previous) {
            // An unfiltered view: a private delta leaves exactly the previous
            // root observable, and any other delta leaves the new source.
            if private_delta {
                view.storage
            } else {
                self.storage.clone()
            }
        } else {
            let retained = view.storage.clone();
            let mut composition = self.composition_from_storage(view.storage);
            update(self, &mut composition);
            // The view is always an occurrence-preserving subset. Equal counts
            // mean nothing is filtered. After an observable change, adopt the
            // complete source root and its prepared indexes. An ignored private
            // delta must retain the old view even when the last exclusion leaves.
            if !std::sync::Arc::ptr_eq(&composition.storage, &retained)
                && composition.storage.facts.len() == self.storage.facts.len()
            {
                composition.storage = self.storage.clone();
            }
            if !std::sync::Arc::ptr_eq(&composition.storage, &retained) {
                self.retain_observable_source(&mut composition);
            }
            composition.storage
        };
        *std::sync::Arc::get_mut(&mut self.observable_projection)
            .expect("detached observable cache")
            .get_mut()
            .expect("observable resource projection") = Some(ObservableResourceProjection {
            classification,
            source: std::sync::Arc::downgrade(&self.storage),
            storage,
        });
    }

    pub(super) fn advance_observable_insertion(
        &mut self,
        previous: &std::sync::Arc<ResourceContextStorage>,
        entry: ResourceEntryId,
    ) {
        let fact = self.fact(entry);
        let private = fact.is_own()
            && fact.memory_range().is_some_and(|range| {
                crate::kernel::block_is_never_address_taken_local(&range.base().block)
            });
        self.advance_observable_projection(previous, private, |source, composition| {
            if private {
                return;
            }
            let fact = source.fact(entry);
            let support = source
                .storage
                .support_occurrence_by_projection
                .get(&entry)
                .copied();
            if support.is_some_and(|support| {
                source.storage.entry_by_occurrence.contains_key(&support)
                    && !composition
                        .storage
                        .entry_by_occurrence
                        .contains_key(&support)
            }) {
                return;
            }
            composition.insert_fact_with_support_at_entry(
                fact.clone(),
                source.storage.supported_by.get(&entry).cloned(),
                support,
                source
                    .storage
                    .support_metadata_by_projection
                    .get(&source.occurrence(entry))
                    .cloned(),
                Some(source.occurrence(entry)),
                entry,
            );
        });
    }

    pub(super) fn advance_observable_removal(
        &mut self,
        previous: &std::sync::Arc<ResourceContextStorage>,
        entry: ResourceEntryId,
    ) {
        self.advance_observable_projection(previous, false, |_, composition| {
            // The source removes descendants first. Mirror each exact entry
            // delta, without discovering a second support-descendant closure.
            if composition.storage.facts.contains_key(&entry) {
                composition.remove_entry_only(entry);
            }
        });
    }

    pub(super) fn advance_observable_rekey(
        &mut self,
        previous: &std::sync::Arc<ResourceContextStorage>,
        fact: &CResourceFact,
    ) {
        self.advance_observable_projection(previous, false, |_, composition| {
            if composition.storage.index.exact.contains_key(fact)
                || composition
                    .storage
                    .expansions_by_support_entry
                    .contains_key(fact)
            {
                composition.rekey_cached_support_entries(fact);
            }
        });
    }

    pub(super) fn advance_observable_expansion(
        &mut self,
        previous: &std::sync::Arc<ResourceContextStorage>,
        occurrence: ResourceOccurrenceId,
    ) {
        self.advance_observable_projection(previous, false, |source, composition| {
            let Some(entry) = composition
                .storage
                .entry_by_occurrence
                .get(&occurrence)
                .copied()
            else {
                return;
            };
            if let Some(expansion) = source
                .storage
                .expansions_by_support_occurrence
                .get(&occurrence)
            {
                let support = composition.fact(entry).clone();
                *composition = composition.clone().with_cached_supported_expansion_arc(
                    occurrence,
                    &support,
                    expansion.clone(),
                );
            } else if composition
                .storage
                .expansions_by_support_occurrence
                .contains_key(&occurrence)
            {
                *composition = composition
                    .clone()
                    .without_cached_supported_expansion_for_occurrence(occurrence);
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn owner(name: &str) -> CResourceFact {
        CResourceFact::own_memory(CMemoryRange::new(
            CMemory::local_pointer(name),
            0u32.into(),
            1u32.into(),
        ))
    }

    fn check(context: &ResourceContext) {
        let observed = context.observable_composition();
        let reference = context.observable_composition_uncached();
        assert_eq!(observed, reference);
        assert_eq!(observed.cmp(&reference), std::cmp::Ordering::Equal);
        use std::hash::{Hash, Hasher};
        let hash = |value: &ResourceContext| {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash(&observed), hash(&reference));
    }

    #[test]
    fn observable_projection_tracks_support_expansions_and_independent_forks() {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(BTreeSet::from(["hidden".into()]));
        let hidden = owner("hidden");
        let addressed = owner("addressed");
        let hidden_view = CResourceFact::view_token("hidden_view".into(), Vec::new());
        let addressed_view = CResourceFact::view_token("addressed_view".into(), Vec::new());
        let root = ResourceContext::new().unchecked_with_fact(addressed.clone());
        check(&root);
        let private_branch = root
            .clone()
            .unchecked_with_fact(hidden.clone())
            .unchecked_with_supported_facts(&hidden, [hidden_view.clone()]);
        check(&private_branch);
        assert!(
            !private_branch
                .observable_composition()
                .facts()
                .contains(&hidden_view)
        );
        let visible_branch = root
            .clone()
            .unchecked_with_supported_facts(&addressed, [addressed_view.clone()]);
        check(&visible_branch);
        assert!(
            visible_branch
                .observable_composition()
                .facts()
                .contains(&addressed_view)
        );
        assert!(!root.facts().contains(&addressed_view));
        let expanded = visible_branch
            .with_cached_supported_expansion(&addressed, vec![addressed_view.clone()]);
        check(&expanded);
        let occurrence = expanded.owned_occurrences_for_fact(&addressed)[0];
        let reset = expanded
            .clone()
            .without_cached_supported_expansion_for_occurrence(occurrence);
        check(&reset);
        let consumed = expanded.without_exact_representation(&addressed).unwrap();
        check(&consumed);
        assert!(
            !consumed
                .observable_composition()
                .facts()
                .contains(&addressed_view)
        );
        let normalized = private_branch.normalized(&PureFactContext::new());
        check(&normalized);
    }

    #[test]
    fn unfiltered_observable_projection_adopts_source_root_without_mirroring() {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(BTreeSet::from(["hidden".into()]));
        let addressed = owner("addressed");
        let addressed_view = CResourceFact::view_token("addressed_view".into(), Vec::new());
        let mut context = ResourceContext::new().unchecked_with_facts(
            (0..64).map(|index| CResourceFact::own_token(format!("unrelated_{index}"), Vec::new())),
        );
        let shares_source = |context: &ResourceContext| {
            std::sync::Arc::ptr_eq(&context.observable_composition().storage, &context.storage)
        };
        assert!(shares_source(&context));
        // Visible inserts, supported views, expansions, and removals keep the
        // warm view on the source root itself; only the source advances, so a
        // warm view allocates exactly what an uncached context does.
        let allocations = |context: &ResourceContext| {
            let before = crate::persistent::persistent_node_allocations();
            let inserted = context.clone().unchecked_with_fact(addressed.clone());
            let removed = inserted.without_exact_representation(&addressed).unwrap();
            drop(removed);
            crate::persistent::persistent_node_allocations() - before
        };
        let cold = ResourceContext::new().unchecked_with_facts(context.iter().cloned());
        assert_eq!(allocations(&context), allocations(&cold));
        context = context.unchecked_with_fact(addressed.clone());
        assert!(shares_source(&context));
        context = context.unchecked_with_supported_facts(&addressed, [addressed_view.clone()]);
        assert!(shares_source(&context));
        context = context.with_cached_supported_expansion(&addressed, vec![addressed_view]);
        assert!(shares_source(&context));
        context = context.without_exact_representation(&addressed).unwrap();
        assert!(shares_source(&context));
        check(&context);
        // A private insertion keeps the previous root as the filtered view.
        let before = context.storage.clone();
        context = context.unchecked_with_fact(owner("hidden"));
        assert!(std::sync::Arc::ptr_eq(
            &context.observable_composition().storage,
            &before
        ));
        check(&context);
    }

    #[test]
    fn observable_projection_invalidates_addressability_changes_and_storage_replacement() {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(BTreeSet::from(["hidden".into()]));
        let hidden = owner("hidden");
        let mut context =
            ResourceContext::new().unchecked_with_facts([hidden.clone(), owner("addressed")]);
        let registry = crate::kernel::capture_block_registries();
        assert!(!context.observable_composition().facts().contains(&hidden));
        crate::kernel::withdraw_never_address_taken_locals(&BTreeSet::from(["hidden".into()]));
        assert!(context.observable_composition().facts().contains(&hidden));
        check(&context);
        crate::kernel::restore_block_registries(&registry);
        assert!(!context.observable_composition().facts().contains(&hidden));
        crate::kernel::clear_never_address_taken_locals();
        assert!(context.observable_composition().facts().contains(&hidden));
        // A missed producer must fall back safely instead of using stale storage.
        context.storage = ResourceContext::new()
            .unchecked_with_fact(owner("other"))
            .storage;
        check(&context);
        assert!(!context.observable_composition().facts().contains(&hidden));
        crate::kernel::set_never_address_taken_locals(BTreeSet::from(["hidden".into()]));
        context = context.unchecked_with_fact(hidden.clone());
        assert!(!context.observable_composition().facts().contains(&hidden));
        std::thread::spawn(move || {
            let _session = crate::kernel::VerificationSession::enter();
            // A context moved to another registry cannot retain its old filter.
            assert!(context.observable_composition().facts().contains(&hidden));
            check(&context);
        })
        .join()
        .unwrap();
    }
}
