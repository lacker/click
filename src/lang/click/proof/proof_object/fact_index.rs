//! `ProofFacts`: the indexed fact store and its index helpers.

use super::*;

impl ProofFacts {
    pub(in crate::lang::click::proof) fn from_ordered(facts: &[Proposition]) -> Self {
        let mut ordered = PersistentSequence::default();
        let mut top_level_exact = PersistentSet::default();
        let mut exact = PersistentSet::default();
        let mut proper_conjuncts = PersistentSet::default();
        let mut by_snapshot_blind = PersistentMap::default();
        let mut bitvector_equalities_by_atom = PersistentMap::default();
        let mut by_quantified_equivalence = PersistentMap::default();
        let mut memory_effect_summaries = PersistentSequence::default();
        let mut implications_by_consequent = PersistentMap::default();
        let mut assumptions = PureFactContext::new();
        let mut implicit_transport_assumptions = PureFactContext::new();
        let mut by_predicate = PersistentMap::default();
        for fact in facts {
            if top_level_exact.contains(fact) {
                continue;
            }
            ordered.push(fact.clone());
            top_level_exact = top_level_exact.with_value(fact.clone());
            by_quantified_equivalence = index_quantified_fact(by_quantified_equivalence, fact);
            if matches!(fact, Proposition::CMemoryEffectSummary { .. }) {
                memory_effect_summaries.push(fact.clone());
            }
            implications_by_consequent =
                index_implication_consequents(implications_by_consequent, fact);
            by_predicate = index_predicate_fact(by_predicate, fact);
            if matches!(fact, Proposition::And(_, _)) {
                proper_conjuncts = index_proper_conjuncts(proper_conjuncts, fact);
                let mut conjuncts = Vec::new();
                collect_owned_atomic_conjuncts(fact, &mut conjuncts);
                for conjunct in conjuncts {
                    by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &conjunct);
                    bitvector_equalities_by_atom =
                        index_bitvector_equality_fact(bitvector_equalities_by_atom, &conjunct);
                    exact = exact.with_value(conjunct);
                }
            }
            by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, fact);
            bitvector_equalities_by_atom =
                index_bitvector_equality_fact(bitvector_equalities_by_atom, fact);
            exact = exact.with_value(fact.clone());
            assumptions = assumptions.assume_proposition(fact.clone());
            implicit_transport_assumptions =
                index_implicit_transport_context(implicit_transport_assumptions, fact);
        }
        Self {
            ordered,
            prioritized: None,
            top_level_exact,
            exact,
            proper_conjuncts,
            by_snapshot_blind,
            bitvector_equalities_by_atom,
            by_quantified_equivalence,
            memory_effect_summaries,
            predicate_unfolded_universal_facts: PersistentSequence::default(),
            implications_by_consequent,
            assumptions,
            implicit_transport_assumptions,
            by_predicate,
        }
    }

    /// Rebuilds a legacy drain view while retaining the exact provenance
    /// indexes owned by facts that remain available. The adapter iterates
    /// only the explicit predicate-unfold delta, never the ambient fact set.
    pub(super) fn resync_ordered_preserving_provenance(&self, facts: &[Proposition]) -> Self {
        let mut successor = Self::from_ordered(facts);
        for fact in self.predicate_unfolded_universal_facts.iter() {
            if successor.contains_top_level(fact) {
                successor = successor.with_predicate_unfold_fact(fact.clone());
            }
        }
        successor
    }

    pub(in crate::lang::click::proof) fn contains(&self, fact: &Proposition) -> bool {
        self.exact.contains(fact)
    }

    pub(in crate::lang::click::proof) fn contains_top_level(&self, fact: &Proposition) -> bool {
        self.top_level_exact.contains(fact)
    }

    pub(in crate::lang::click::proof) fn with_fact(&self, fact: Proposition) -> Self {
        if self.top_level_exact.contains(&fact) {
            return self.clone();
        }
        let mut exact = self.exact.clone();
        let mut proper_conjuncts = self.proper_conjuncts.clone();
        let mut by_snapshot_blind = self.by_snapshot_blind.clone();
        let mut bitvector_equalities_by_atom = self.bitvector_equalities_by_atom.clone();
        let by_quantified_equivalence =
            index_quantified_fact(self.by_quantified_equivalence.clone(), &fact);
        let mut memory_effect_summaries = self.memory_effect_summaries.clone();
        if matches!(fact, Proposition::CMemoryEffectSummary { .. }) {
            memory_effect_summaries.push(fact.clone());
        }
        let implications_by_consequent =
            index_implication_consequents(self.implications_by_consequent.clone(), &fact);
        if matches!(fact, Proposition::And(_, _)) {
            proper_conjuncts = index_proper_conjuncts(proper_conjuncts, &fact);
            let mut conjuncts = Vec::new();
            collect_owned_atomic_conjuncts(&fact, &mut conjuncts);
            for conjunct in conjuncts {
                by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &conjunct);
                bitvector_equalities_by_atom =
                    index_bitvector_equality_fact(bitvector_equalities_by_atom, &conjunct);
                exact = exact.with_value(conjunct);
            }
        }
        by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &fact);
        bitvector_equalities_by_atom =
            index_bitvector_equality_fact(bitvector_equalities_by_atom, &fact);
        exact = exact.with_value(fact.clone());
        let mut ordered = self.ordered.clone();
        ordered.push(fact.clone());
        let implicit_transport_assumptions =
            index_implicit_transport_context(self.implicit_transport_assumptions.clone(), &fact);
        Self {
            ordered,
            prioritized: self.prioritized.clone(),
            top_level_exact: self.top_level_exact.with_value(fact.clone()),
            exact,
            proper_conjuncts,
            by_snapshot_blind,
            bitvector_equalities_by_atom,
            by_quantified_equivalence,
            memory_effect_summaries,
            predicate_unfolded_universal_facts: self.predicate_unfolded_universal_facts.clone(),
            implications_by_consequent,
            assumptions: self.assumptions.clone().assume_proposition(fact.clone()),
            implicit_transport_assumptions,
            by_predicate: index_predicate_fact(self.by_predicate.clone(), &fact),
        }
    }

    pub(in crate::lang::click::proof) fn with_predicate_unfold_fact(
        &self,
        fact: Proposition,
    ) -> Self {
        let is_universal = matches!(fact, Proposition::ForAll { .. });
        let mut successor = self.with_fact(fact.clone());
        if is_universal
            && !successor
                .predicate_unfolded_universal_facts
                .iter()
                .any(|candidate| candidate == &fact)
        {
            successor.predicate_unfolded_universal_facts.push(fact);
        }
        successor
    }

    /// Materializes one selected separation from the compact resource-
    /// composition index. This is target-driven: unrelated resource pairs
    /// remain implicit, while a successful result is an exact fact for the
    /// ordinary `Assumption` checker in the new point goal.
    pub(super) fn with_selected_resource_separation(&self, goal: &Proposition) -> Self {
        if matches!(
            goal,
            Proposition::CResourceSeparate { .. } | Proposition::CMemoryDisjoint { .. }
        ) && !self.contains(goal)
            && self.assumptions.proves(goal)
        {
            self.with_fact(goal.clone())
        } else {
            self.clone()
        }
    }

    /// Materializes one selected equality across a checked chain of load
    /// variables. This keeps the ordinary `Assumption` checker exact while
    /// allowing a new point goal to consume equality transport explicitly
    /// carried through the preceding statement. Selection follows only the
    /// goal's indexed equality buckets; unrelated ambient equalities remain
    /// implicit and are never visited.
    pub(super) fn with_selected_load_equality_bridge(&self, goal: &Proposition) -> Self {
        if self.pure_assumption_available(goal)
            || !matches!(
                goal,
                Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true)
            )
        {
            return self.clone();
        }
        let candidates = self.bitvector_equalities_mentioning(goal);
        if !candidates.is_empty()
            && premise_bridged_by_load_variable_chain_with_origins(
                goal,
                &candidates,
                &self.assumptions,
            )
        {
            self.with_fact(goal.clone())
        } else {
            self.clone()
        }
    }

    pub(in crate::lang::click::proof) fn assumptions(&self) -> &PureFactContext {
        &self.assumptions
    }

    pub(super) fn memory_effect_summaries(&self) -> impl Iterator<Item = &Proposition> {
        self.memory_effect_summaries.iter()
    }

    /// Exact proper-conjunct membership with the same condition-polarity
    /// equivalence as the legacy structural checker.
    pub(in crate::lang::click::proof) fn contains_proper_conjunct(
        &self,
        required: &Proposition,
    ) -> bool {
        self.proper_conjuncts.contains(required)
            || condition_polarity_forms(required)
                .iter()
                .any(|form| self.proper_conjuncts.contains(form))
    }

    /// Exact or direct-load-materialization-equivalent availability used by
    /// the deterministic rewrite rule. Unlike snapshot check, this does not
    /// admit polarity changes or a semantic bridge beyond normalization.
    pub(in crate::lang::click::proof) fn materialization_available(
        &self,
        required: &Proposition,
    ) -> bool {
        self.exact.contains(required)
    }

    /// Availability of a proposition to the explicit pure `assumption`
    /// judgment used inside point proofs. This deliberately excludes
    /// cross-effect snapshot transport: such a transport needs its own
    /// retained proof step before a later assumption may consume it.
    pub(in crate::lang::click::proof) fn pure_assumption_available(
        &self,
        required: &Proposition,
    ) -> bool {
        self.materialization_available(required) || self.quantified_fact_available(required)
    }

    pub(in crate::lang::click::proof) fn implicit_transport_assumptions(&self) -> &PureFactContext {
        &self.implicit_transport_assumptions
    }

    /// Adds one statement's selected successor context while retaining the
    /// old ambient order by shared prefix. The statement delta is explicit,
    /// so insertion work is proportional only to that delta and index height.
    pub(in crate::lang::click::proof) fn with_statement_facts(
        &self,
        facts: Vec<Proposition>,
    ) -> Self {
        let ordered = self.ordered.clone();
        let parent = self.prioritized.clone();
        let mut successor = self.clone();
        for fact in &facts {
            successor = successor.with_fact(fact.clone());
        }
        successor.ordered = ordered;
        successor.prioritized = Some(Arc::new(PrioritizedProofFacts {
            parent,
            facts: Arc::new(facts),
        }));
        successor
    }

    /// Availability accepted by explicit check, answered from persistent
    /// indexes. Snapshot-blind buckets only select structurally compatible
    /// candidates; the kernel still proves every cross-snapshot match.
    pub(in crate::lang::click::proof) fn available_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> bool {
        if self.exact_available_across_effects(required, framing) {
            return true;
        }

        self.quantified_fact_available(required)
    }

    /// Returns one actual available fact accepted by explicit check. Smart
    /// syntax selection needs the retained fact, not merely a yes/no answer:
    /// its recorded surface form may carry a statement snapshot that the
    /// freshly lowered theorem requirement no longer exposes.
    pub(super) fn matching_fact_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> Option<Proposition> {
        let keys = [snapshot_blind_proposition_key(required)];
        let mut indexed_candidates = Vec::new();
        for key in &keys {
            if let Some(bucket) = self.by_snapshot_blind.get(key) {
                for candidate in bucket.iter() {
                    if !indexed_candidates.contains(candidate) {
                        indexed_candidates.push(candidate.clone());
                    }
                }
            }
        }
        // Preserve the legacy selector's canonical materialization choice,
        // but search only the requirement's persistent shape bucket. The
        // chosen sibling snapshot can have a stable recorded `at(...)`
        // form even when the freshly lowered requirement is also present.
        if let Some(candidate) = exactly_available_fact(required, &indexed_candidates) {
            return Some(candidate.clone());
        }
        if self.exact.contains(required) {
            return Some(required.clone());
        }
        if let Some(form) = condition_polarity_forms(required)
            .into_iter()
            .find(|form| self.exact.contains(form))
        {
            return Some(form);
        }

        if let Some(quantified) = self.matching_quantified_fact(required) {
            return Some(quantified);
        }

        let mut candidates = Vec::new();
        for key in keys {
            let Some(bucket) = self.by_snapshot_blind.get(&key) else {
                continue;
            };
            for candidate in bucket.iter() {
                if !candidates.contains(candidate) {
                    candidates.push(candidate.clone());
                }
                if candidate == required
                    || separation_bridged_fact_is_available(
                        required,
                        std::slice::from_ref(candidate),
                        &self.assumptions,
                        framing,
                    )
                {
                    return Some(candidate.clone());
                }
            }
        }
        separation_bridged_fact_is_available(required, &candidates, &self.assumptions, framing)
            .then(|| required.clone())
    }

    pub(super) fn matching_quantified_fact(&self, required: &Proposition) -> Option<Proposition> {
        self.matching_quantified_facts(required).into_iter().next()
    }

    pub(super) fn matching_quantified_facts(&self, required: &Proposition) -> Vec<Proposition> {
        quantified_equivalence_index_key(required)
            .and_then(|key| self.by_quantified_equivalence.get(&key))
            .into_iter()
            .flat_map(PersistentSequence::iter)
            .filter(|candidate| {
                quantified_binder_equivalent(required, candidate)
                    || quantified_equivalent_available_fact(
                        required,
                        std::slice::from_ref(candidate),
                    )
                    .is_some()
            })
            .cloned()
            .collect()
    }

    pub(super) fn quantified_fact_available(&self, required: &Proposition) -> bool {
        self.matching_quantified_fact(required).is_some()
    }

    pub(super) fn contains_discharged_implication_consequent(
        &self,
        required: &Proposition,
    ) -> bool {
        let keys = vec![snapshot_blind_proposition_key(required)];
        keys.into_iter()
            .filter_map(|key| self.implications_by_consequent.get(&key))
            .flat_map(PersistentSequence::iter)
            .any(|candidate| {
                &candidate.consequent == required
                    && candidate
                        .antecedents
                        .iter()
                        .all(|antecedent| self.available_across_effects(antecedent, &[]))
            })
    }

    pub(in crate::lang::click::proof) fn exact_available_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> bool {
        if self.contains(required)
            || condition_polarity_forms(required)
                .iter()
                .any(|form| self.exact.contains(form))
        {
            return true;
        }

        let keys = [snapshot_blind_proposition_key(required)];
        let mut candidates = Vec::new();
        for key in keys {
            if let Some(bucket) = self.by_snapshot_blind.get(&key) {
                for candidate in bucket.iter() {
                    if !candidates.contains(candidate) {
                        candidates.push(candidate.clone());
                    }
                }
            }
        }
        if candidates.is_empty() {
            return false;
        }
        separation_bridged_fact_is_available(required, &candidates, &self.assumptions, framing)
    }

    pub(in crate::lang::click::proof) fn directly_conflicts_with(
        &self,
        fact: &Proposition,
    ) -> bool {
        directly_conflicts_with_normalized_index(&self.exact, fact)
    }

    /// Returns exact equality facts attached to terms occurring in this
    /// proposition. Selection cost follows the proposition and the matching
    /// equality buckets; unrelated ambient equalities are never visited.
    pub(super) fn bitvector_equalities_mentioning(
        &self,
        proposition: &Proposition,
    ) -> Vec<Proposition> {
        let mut atoms = BTreeSet::new();
        collect_proposition_bitvector_atoms(proposition, &mut atoms);
        let mut equalities = Vec::new();
        for atom in atoms {
            if let Some(bucket) = self.bitvector_equalities_by_atom.get(&atom) {
                for equality in bucket.iter() {
                    equalities.push(equality.clone());
                }
            }
        }
        equalities
    }

    /// The facts this context introduced after `ancestor`, oldest first.
    ///
    /// Both fact stores are parent-linked and append-only, so the delta is
    /// recovered by walking only the appended suffixes — prioritized
    /// statement batches first, then ordinary insertions — and pointer
    /// identity proves the shared history. Returns `None` when `ancestor`
    /// is not this context's ancestor. This is the output-sensitive
    /// introduction delta the execution sibling-split joins consume.
    pub(in crate::lang::click::proof) fn introduced_since(
        &self,
        ancestor: &Self,
    ) -> Option<Vec<Proposition>> {
        let mut new_batches = Vec::new();
        let mut current = self.prioritized.clone();
        loop {
            match (&current, &ancestor.prioritized) {
                (Some(node), Some(ancestor_head)) if Arc::ptr_eq(node, ancestor_head) => break,
                (None, None) => break,
                (Some(node), _) => {
                    new_batches.push(node.facts.clone());
                    current = node.parent.clone();
                }
                (None, Some(_)) => return None,
            }
        }
        let ordered_suffix = self.ordered.suffix_since(&ancestor.ordered)?;
        let mut introduced = Vec::new();
        for batch in new_batches.iter().rev() {
            introduced.extend(batch.iter().cloned());
        }
        introduced.extend(ordered_suffix);
        Some(introduced)
    }

    pub(in crate::lang::click::proof) fn to_vec(&self) -> Vec<Proposition> {
        let mut ordered = Vec::new();
        let mut seen = BTreeSet::new();
        let mut batch = self.prioritized.as_deref();
        while let Some(current) = batch {
            for fact in current.facts.iter() {
                if seen.insert(fact.clone()) {
                    ordered.push(fact.clone());
                }
            }
            batch = current.parent.as_deref();
        }
        for fact in self.ordered.iter() {
            if seen.insert(fact.clone()) {
                ordered.push(fact.clone());
            }
        }
        ordered
    }

    pub(in crate::lang::click::proof) fn mentioning_predicate(
        &self,
        name: &String,
    ) -> impl Iterator<Item = &Proposition> {
        self.by_predicate
            .get(name)
            .into_iter()
            .flat_map(PersistentSequence::iter)
    }

    #[cfg(test)]
    pub(super) fn lookup_comparisons(&self, fact: &Proposition) -> usize {
        self.exact.lookup_comparisons(fact)
    }

    #[cfg(test)]
    pub(super) fn equality_atom_lookup_comparisons(&self, term: &Bitvector32Term) -> usize {
        let key = bitvector_equality_atom_key(term).expect("test term should be an indexed atom");
        self.bitvector_equalities_by_atom.lookup_comparisons(&key)
    }
}

pub(super) fn index_snapshot_fact(
    mut by_snapshot_blind: PersistentMap<
        SnapshotBlindPropositionKey,
        PersistentSequence<Proposition>,
    >,
    fact: &Proposition,
) -> PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Proposition>> {
    for key in [snapshot_blind_proposition_key(fact)] {
        if !key.forgets_a_snapshot() {
            continue;
        }
        let mut bucket = by_snapshot_blind.get(&key).cloned().unwrap_or_default();
        if !bucket.iter().any(|candidate| candidate == fact) {
            bucket.push(fact.clone());
            by_snapshot_blind = by_snapshot_blind.with_inserted(key, bucket);
        }
    }
    by_snapshot_blind
}

pub(super) fn index_bitvector_equality_fact(
    mut index: PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Proposition>> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = fact else {
        return index;
    };
    for term in [left.as_ref(), right.as_ref()] {
        let Some(key) = bitvector_equality_atom_key(term) else {
            continue;
        };
        let mut bucket = index.get(&key).cloned().unwrap_or_default();
        bucket.push(fact.clone());
        index = index.with_inserted(key, bucket);
    }
    index
}

pub(super) fn bitvector_equality_atom_key(
    term: &Bitvector32Term,
) -> Option<BitvectorEqualityAtomKey> {
    match term {
        Bitvector32Term::Constant(value) => Some(BitvectorEqualityAtomKey::Constant(*value)),
        Bitvector32Term::Variable(variable) => Some(BitvectorEqualityAtomKey::Variable(*variable)),
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(pointer.as_ref(), &mut hasher);
            Some(BitvectorEqualityAtomKey::MemoryLoad {
                memory: memory.arena_id(),
                pointer_hash: std::hash::Hasher::finish(&hasher),
            })
        }
        _ => None,
    }
}

pub(super) fn collect_proposition_bitvector_atoms(
    proposition: &Proposition,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match proposition {
        Proposition::ConditionIs(condition, _) => {
            collect_condition_bitvector_atoms(condition, atoms)
        }
        Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. }
        | Proposition::Not(body) => collect_proposition_bitvector_atoms(body, atoms),
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_bitvector_atoms(left, atoms);
            collect_proposition_bitvector_atoms(right, atoms);
        }
        _ => {}
    }
}

pub(super) fn collect_condition_bitvector_atoms(
    condition: &ConditionTerm,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            collect_bitvector_atoms(left, atoms);
            collect_bitvector_atoms(right, atoms);
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_bitvector_atoms(left, atoms);
            collect_pointer_offset_bitvector_atoms(right, atoms);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_offset_bitvector_atoms(&left.offset, atoms);
            collect_pointer_offset_bitvector_atoms(&right.offset, atoms);
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
    }
}

pub(super) fn collect_bitvector_atoms(
    term: &Bitvector32Term,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    if let Some(atom) = bitvector_equality_atom_key(term) {
        atoms.insert(atom);
    }
    match term {
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            collect_bitvector_atoms(left, atoms);
            collect_bitvector_atoms(right, atoms);
        }
        Bitvector32Term::BitwiseNot(value) => collect_bitvector_atoms(value, atoms),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bitvector_atoms(condition, atoms);
            collect_bitvector_atoms(then_term, atoms);
            collect_bitvector_atoms(else_term, atoms);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_atoms(start, atoms);
            collect_bitvector_atoms(end, atoms);
            collect_bitvector_atoms(initial, atoms);
            collect_bitvector_atoms(body, atoms);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_atoms(argument, atoms);
            }
        }
        Bitvector32Term::MemoryLoad(_, pointer) => {
            collect_pointer_offset_bitvector_atoms(&pointer.offset, atoms)
        }
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
    }
}

pub(super) fn collect_pointer_offset_bitvector_atoms(
    offset: &PointerOffsetTerm,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match offset {
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_bitvector_atoms(left, atoms);
            collect_pointer_offset_bitvector_atoms(right, atoms);
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => collect_bitvector_atoms(value, atoms),
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
    }
}

pub(super) fn index_quantified_fact(
    mut index: PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Proposition>> {
    let Some(key) = quantified_equivalence_index_key(fact) else {
        return index;
    };
    let mut bucket = index.get(&key).cloned().unwrap_or_default();
    if !bucket.iter().any(|candidate| candidate == fact) {
        bucket.push(fact.clone());
        index = index.with_inserted(key, bucket);
    }
    index
}

pub(super) fn index_implication_consequents(
    mut index: PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>>,
    fact: &Proposition,
) -> PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>> {
    let mut antecedents = PersistentSequence::default();
    let mut current = fact;
    while let Proposition::Implies(antecedent, consequent) = current {
        antecedents.push(antecedent.as_ref().clone());
        let candidate = ImplicationCandidate {
            antecedents: antecedents.clone(),
            consequent: consequent.as_ref().clone(),
        };
        let normalized = consequent.clone();
        let mut keys = vec![snapshot_blind_proposition_key(consequent)];
        let normalized_key = snapshot_blind_proposition_key(&normalized);
        if !keys.contains(&normalized_key) {
            keys.push(normalized_key);
        }
        for key in keys {
            let mut bucket = index.get(&key).cloned().unwrap_or_default();
            bucket.push(candidate.clone());
            index = index.with_inserted(key, bucket);
        }
        current = consequent;
    }
    index
}

pub(super) fn index_proper_conjuncts(
    mut index: PersistentSet<Proposition>,
    fact: &Proposition,
) -> PersistentSet<Proposition> {
    let Proposition::And(left, right) = fact else {
        return index;
    };
    for conjunct in [left.as_ref(), right.as_ref()] {
        index = index.with_value(conjunct.clone());
        index = index_proper_conjuncts(index, conjunct);
    }
    index
}

pub(super) fn collect_surface_conjunct_leaves(
    proposition: &ClickProposition,
    leaves: &mut Vec<ClickProposition>,
) {
    match proposition {
        ClickProposition::And(left, right) => {
            collect_surface_conjunct_leaves(left, leaves);
            collect_surface_conjunct_leaves(right, leaves);
        }
        leaf => leaves.push(leaf.clone()),
    }
}

pub(super) fn index_implicit_transport_context(
    mut implicit: PureFactContext,
    fact: &Proposition,
) -> PureFactContext {
    if is_implicit_fact_transport_context(fact) {
        implicit = implicit.assume_proposition(fact.clone());
    }
    implicit
}

pub(super) fn directly_conflicts_with_normalized_index(
    exact: &PersistentSet<Proposition>,
    fact: &Proposition,
) -> bool {
    match fact {
        Proposition::And(left, right) => {
            directly_conflicts_with_normalized_index(exact, left)
                || directly_conflicts_with_normalized_index(exact, right)
        }
        Proposition::ConditionIs(condition, value) => {
            exact.contains(&Proposition::ConditionIs(condition.clone(), !value))
        }
        Proposition::Not(body) => exact.contains(body),
        other => exact.contains(&Proposition::Not(Box::new(other.clone()))),
    }
}

pub(super) fn index_predicate_fact(
    mut index: PersistentMap<String, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<String, PersistentSequence<Proposition>> {
    let mut names = BTreeSet::new();
    collect_fact_predicate_names(fact, &mut names);
    for name in names {
        let mut facts = index.get(&name).cloned().unwrap_or_default();
        facts.push(fact.clone());
        index = index.with_inserted(name, facts);
    }
    index
}

pub(super) fn collect_fact_predicate_names(fact: &Proposition, names: &mut BTreeSet<String>) {
    match fact {
        Proposition::Predicate { name, .. } => {
            names.insert(name.clone());
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_fact_predicate_names(left, names);
            collect_fact_predicate_names(right, names);
        }
        Proposition::Not(body)
        | Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. } => collect_fact_predicate_names(body, names),
        _ => {}
    }
}

pub(super) fn collect_owned_atomic_conjuncts(fact: &Proposition, output: &mut Vec<Proposition>) {
    match fact {
        Proposition::And(left, right) => {
            collect_owned_atomic_conjuncts(left, output);
            collect_owned_atomic_conjuncts(right, output);
        }
        _ => output.push(fact.clone()),
    }
}
