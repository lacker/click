use super::*;

impl ResourceContext {
    pub fn new() -> Self {
        Self::default()
    }

    fn facts_mut(&mut self) -> &mut Vec<CResourceFact> {
        self.index = std::sync::Arc::new(std::sync::OnceLock::new());
        std::sync::Arc::make_mut(&mut self.facts)
    }

    fn index(&self) -> &ResourceContextIndex {
        self.index.get_or_init(|| {
            let mut index = ResourceContextIndex::default();
            for (position, fact) in self.facts.iter().enumerate() {
                crate::instrumentation::record_deterministic_work(1);
                index.exact.entry(fact.clone()).or_default().push(position);
                index
                    .by_resource
                    .entry(fact.resource().clone())
                    .or_default()
                    .push(position);
                if let Some(range) = fact.memory_range() {
                    let mode = fact.is_own();
                    index
                        .memory_by_block
                        .entry(range.base().block.clone())
                        .or_default()
                        .push(position);
                    index
                        .memory_starts
                        .entry((range.base().block.clone(), mode, range.start().clone()))
                        .or_default()
                        .push(position);
                    index
                        .memory_ends
                        .entry((range.base().block.clone(), mode, range.end().clone()))
                        .or_default()
                        .push(position);
                    if let (Some(start), Some(end)) =
                        (range.start().as_const(), range.end().as_const())
                    {
                        index
                            .concrete_memory_by_base
                            .entry((range.base().clone(), mode))
                            .or_default()
                            .entry((start, end))
                            .or_default()
                            .push(position);
                    }
                } else if let CResource::Composite { name, arguments }
                | CResource::Token { name, arguments } = fact.resource()
                {
                    index
                        .exact_shapes
                        .entry((fact.family(), name.clone(), arguments.len()))
                        .or_default()
                        .push(position);
                }
            }
            index
        })
    }

    fn memory_block_facts(&self, block: &PointerBlock) -> impl Iterator<Item = &CResourceFact> {
        self.index()
            .memory_by_block
            .get(block)
            .into_iter()
            .flatten()
            .map(|index| &self.facts[*index])
    }

    /// Necessary-shape candidates for proof-aware direct resource matching.
    /// Snapshot-insensitive matching cannot change a pointer block, resource
    /// family, composite/token name, or arity, so unrelated facts need not
    /// enter the expensive memory-resolution comparator.
    pub(in crate::kernel) fn direct_match_candidates(
        &self,
        fact: &CResourceFact,
    ) -> impl Iterator<Item = &CResourceFact> {
        self.direct_match_candidate_positions(fact)
            .into_iter()
            .flatten()
            .map(|index| &self.facts[*index])
    }

    fn direct_match_candidate_positions(&self, fact: &CResourceFact) -> Option<&Vec<usize>> {
        match fact.resource() {
            CResource::Memory(range) => self.index().memory_by_block.get(&range.base().block),
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => self
                .index()
                .exact_shapes
                .get(&(fact.family(), name.clone(), arguments.len())),
        }
    }

    /// Adds a resource fact without checking validity or normalizing the
    /// context.
    ///
    /// Prefer `try_compose_with_fact` when proposition assumptions are
    /// available.
    pub fn unchecked_with_fact(mut self, fact: CResourceFact) -> Self {
        self.facts_mut().push(fact);
        self
    }

    /// Adds resource facts without checking validity or normalizing the
    /// context.
    ///
    /// Prefer `try_compose_with_facts` when proposition assumptions are
    /// available.
    pub fn unchecked_with_facts(mut self, facts: impl IntoIterator<Item = CResourceFact>) -> Self {
        self.facts_mut().extend(facts);
        self
    }

    pub fn try_compose_with_fact(
        self,
        fact: CResourceFact,
        assumptions: &Assumptions,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_with_facts(std::iter::once(fact), assumptions)
    }

    pub fn try_compose_with_facts(
        self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &Assumptions,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_with_facts_delaying_normalization(facts, assumptions)
            .map(|context| context.normalized(assumptions))
    }

    pub(crate) fn try_compose_with_facts_delaying_normalization(
        self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &Assumptions,
    ) -> Result<Self, ResourceContextValidityError> {
        let context = self.unchecked_with_facts(facts);
        if let Some(error) = context.validity_error(assumptions) {
            return Err(error);
        }
        Ok(context)
    }

    /// Extends a context whose validity has already been checked, validating
    /// only pairs that contain at least one newly added fact.
    pub(in crate::kernel) fn try_compose_into_valid_context_delaying_normalization(
        mut self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &Assumptions,
    ) -> Result<Self, ResourceContextValidityError> {
        let first_new = self.facts.len();
        self.facts_mut().extend(facts);
        for right_index in first_new..self.facts.len() {
            let right = &self.facts[right_index];
            let Some(right_range) = right.memory_own_range() else {
                continue;
            };
            let same_base_concrete = right_range
                .start()
                .as_const()
                .zip(right_range.end().as_const())
                .and_then(|(start, end)| {
                    let block_positions = self
                        .index()
                        .memory_by_block
                        .get(&right_range.base().block)?;
                    let ranges = self
                        .index()
                        .concrete_memory_by_base
                        .get(&(right_range.base().clone(), true))?;
                    let represented = ranges.values().map(Vec::len).sum::<usize>();
                    let owned_in_block = block_positions
                        .iter()
                        .filter(|position| self.facts[**position].memory_own_range().is_some())
                        .count();
                    (represented == owned_in_block).then_some((start, end, ranges))
                });
            if let Some((start, end, ranges)) = same_base_concrete {
                let key = (start, end);
                let mut candidates = BTreeSet::new();
                if let Some(duplicates) = ranges.get(&key) {
                    candidates.extend(
                        duplicates
                            .iter()
                            .copied()
                            .filter(|position| *position != right_index),
                    );
                }
                if let Some((_, positions)) = ranges.range(..key).next_back()
                    && let Some(position) = positions.last()
                {
                    candidates.insert(*position);
                }
                if let Some((_, positions)) = ranges
                    .range((std::ops::Bound::Excluded(key), std::ops::Bound::Unbounded))
                    .next()
                    && let Some(position) = positions.first()
                {
                    candidates.insert(*position);
                }
                for left_index in candidates {
                    crate::instrumentation::record_deterministic_work(1);
                    let left = &self.facts[left_index];
                    if let Some(error) = resource_family_algebra(left.family()).pair_validity_error(
                        left,
                        right,
                        assumptions,
                    ) {
                        return Err(error);
                    }
                }
                continue;
            }
            for left in self
                .memory_block_facts(&right_range.base().block)
                .take_while(|left| !std::ptr::eq(*left, right))
            {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(error) = resource_family_algebra(left.family()).pair_validity_error(
                    left,
                    right,
                    assumptions,
                ) {
                    return Err(error);
                }
            }
        }
        Ok(self)
    }

    pub fn facts(&self) -> &[CResourceFact] {
        &self.facts
    }

    pub fn validity_error(
        &self,
        assumptions: &Assumptions,
    ) -> Option<ResourceContextValidityError> {
        for positions in self.index().memory_by_block.values() {
            let owned = positions
                .iter()
                .filter_map(|index| {
                    let fact = &self.facts[*index];
                    fact.memory_own_range().map(|range| (fact, range))
                })
                .collect::<Vec<_>>();
            let one_concrete_base = owned.first().map(|(_, range)| range.base()).filter(|base| {
                owned.iter().all(|(_, range)| {
                    range.base() == *base
                        && range.start().as_const().is_some()
                        && range.end().as_const().is_some()
                })
            });
            if one_concrete_base.is_some() {
                let mut ordered = owned;
                ordered.sort_by_key(|(_, range)| {
                    (
                        range.start().as_const().unwrap(),
                        range.end().as_const().unwrap(),
                    )
                });
                let mut furthest: Option<(&CResourceFact, &CMemoryRange)> = None;
                for (fact, range) in ordered {
                    crate::instrumentation::record_deterministic_work(1);
                    if let Some((left, left_range)) = furthest {
                        if let Some(error) = resource_family_algebra(left.family())
                            .pair_validity_error(left, fact, assumptions)
                        {
                            return Some(error);
                        }
                        if range.end().as_const().unwrap() > left_range.end().as_const().unwrap() {
                            furthest = Some((fact, range));
                        }
                    } else {
                        furthest = Some((fact, range));
                    }
                }
                continue;
            }
            for (offset, left_index) in positions.iter().enumerate() {
                let left = &self.facts[*left_index];
                if left.memory_own_range().is_none() {
                    continue;
                }
                for right_index in &positions[offset + 1..] {
                    crate::instrumentation::record_deterministic_work(1);
                    let right = &self.facts[*right_index];
                    if right.memory_own_range().is_none() {
                        continue;
                    }
                    if let Some(error) = resource_family_algebra(left.family()).pair_validity_error(
                        left,
                        right,
                        assumptions,
                    ) {
                        return Some(error);
                    }
                }
            }
        }
        None
    }

    pub fn is_valid(&self, assumptions: &Assumptions) -> bool {
        self.validity_error(assumptions).is_none()
    }

    pub fn observable_facts(
        &self,
        assumptions: &Assumptions,
    ) -> Result<Vec<Proposition>, ResourceContextValidityError> {
        if let Some(error) = self.validity_error(assumptions) {
            return Err(error);
        }
        Ok(self.observable_facts_assuming_valid(assumptions))
    }

    /// Projects facts from a resource composition whose validity has already
    /// been established by an enclosing resource law.
    pub(crate) fn observable_facts_assuming_valid(
        &self,
        assumptions: &Assumptions,
    ) -> Vec<Proposition> {
        let mut propositions = Vec::new();
        for family in ResourceFamily::ALL {
            let facts = self
                .facts
                .iter()
                .filter(|fact| fact.family() == family)
                .collect::<Vec<_>>();
            propositions
                .extend(resource_family_algebra(family).observable_facts(&facts, assumptions));
        }
        propositions.extend(self.cross_family_separate_facts());
        propositions
    }

    fn cross_family_separate_facts(&self) -> Vec<Proposition> {
        let owned = self
            .facts
            .iter()
            .filter_map(CResourceFact::owned_resource)
            .collect::<Vec<_>>();
        let mut propositions = Vec::new();
        for i in 0..owned.len() {
            for right in &owned[i + 1..] {
                let left = owned[i];
                if left.family() == right.family() {
                    continue;
                }
                propositions.push(Proposition::CResourceSeparate {
                    left: (*left).clone(),
                    right: (**right).clone(),
                });
            }
        }
        propositions
    }

    pub fn satisfies_fact(&self, fact: &CResourceFact, assumptions: &Assumptions) -> bool {
        if self.index().exact.contains_key(fact) {
            return true;
        }
        // Exact ownership of a resource definitionally includes its exact
        // view. The resource-key index already erases access mode and owned
        // quantity, so answer this common core-projection query without
        // entering proof-aware memory/snapshot entailment.
        if fact.is_view() && self.index().by_resource.contains_key(fact.resource()) {
            return true;
        }
        if crate::instrumentation::measure_operation(
            "kernel",
            "resource satisfaction",
            "resource satisfaction: indexed direct entailment",
            || {
                self.direct_match_candidates(fact)
                    .any(|available| resource_fact_entails(available, fact, assumptions))
            },
        ) {
            return true;
        }
        // A required fact may span several adjacent held resources; merge
        // them and retry once. Only memory resources have a split/merge
        // algebra: token and composite entailment is decided one fact at a
        // time above. Normalizing an unrelated ambient memory context while
        // looking for a missing token or composite makes an exact resource
        // query depend on every symbolic range the caller happens to hold.
        if fact.family() != ResourceFamily::Memory {
            return false;
        }
        // Normalization can only merge facts within one access mode. A
        // viewed context cannot acquire ownership by normalizing, so avoid
        // scanning unrelated composite views for an impossible owned-memory
        // query.
        if fact.is_own()
            && !self
                .direct_match_candidates(fact)
                .any(CResourceFact::is_own)
        {
            return false;
        }
        let normalized = crate::instrumentation::measure_operation(
            "kernel",
            "resource satisfaction",
            "resource satisfaction: normalization fallback",
            || self.clone().normalized(assumptions),
        );
        normalized.facts.len() < self.facts.len()
            && normalized
                .direct_match_candidates(fact)
                .any(|available| resource_fact_entails(available, fact, assumptions))
    }

    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }

    pub(in crate::kernel) fn permits_memory_read(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &Assumptions,
    ) -> bool {
        if self.permits_memory_read_structurally(pointer, byte_width, assumptions) {
            return true;
        }
        self.memory_block_facts(&pointer.block).any(|resource| {
            memory_resource_fact_permits_read(resource, pointer, byte_width, assumptions)
        })
    }

    pub(in crate::kernel) fn permits_memory_read_structurally(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &Assumptions,
    ) -> bool {
        for resource in self.memory_block_facts(&pointer.block) {
            let Some(range) = resource_fact_read_core_range(resource) else {
                continue;
            };
            if pointer_has_structural_range_base(pointer, range.base())
                && memory_resource_fact_permits_read(resource, pointer, byte_width, assumptions)
            {
                return true;
            }
        }
        false
    }

    pub(in crate::kernel) fn memory_write_range(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &Assumptions,
    ) -> Option<&CMemoryRange> {
        for resource in self.memory_block_facts(&pointer.block) {
            let CResourceFact::Own(CResource::Memory(range), _) = resource else {
                continue;
            };
            if pointer_has_structural_range_base(pointer, range.base())
                && memory_resource_fact_permits_write(resource, pointer, byte_width, assumptions)
            {
                return Some(range);
            }
        }
        self.facts.iter().find_map(|resource| {
            memory_resource_fact_permits_write(resource, pointer, byte_width, assumptions)
                .then(|| resource.memory_own_range())
                .flatten()
        })
    }

    pub fn without_fact(self, fact: &CResourceFact, assumptions: &Assumptions) -> Option<Self> {
        self.without_fact_delaying_normalization(fact, assumptions)
            .map(|context| context.normalized(assumptions))
    }

    pub(in crate::kernel) fn without_fact_delaying_normalization(
        mut self,
        fact: &CResourceFact,
        assumptions: &Assumptions,
    ) -> Option<Self> {
        self.consume_fact_without_normalizing(fact, assumptions)
            .then_some(self)
    }

    pub(crate) fn without_exact_representation(mut self, fact: &CResourceFact) -> Option<Self> {
        let index = *self.index().exact.get(fact)?.first()?;
        self.facts_mut().remove(index);
        Some(self)
    }

    /// Consumes several facts while postponing whole-context normalization
    /// until the end. If a required fact is only available after adjacent
    /// resources are merged, normalize once at that point and retry it.
    pub fn without_facts(self, facts: &[CResourceFact], assumptions: &Assumptions) -> Option<Self> {
        let mut context = self;
        for fact in facts {
            if context.consume_fact_without_normalizing(fact, assumptions) {
                continue;
            }
            context = context.normalized(assumptions);
            if !context.consume_fact_without_normalizing(fact, assumptions) {
                return None;
            }
        }
        Some(context.normalized(assumptions))
    }

    fn consume_fact_without_normalizing(
        &mut self,
        fact: &CResourceFact,
        assumptions: &Assumptions,
    ) -> bool {
        let algebra = resource_family_algebra(fact.family());
        let mut candidates = self
            .index()
            .exact
            .get(fact)
            .into_iter()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        let exact_candidates = candidates.iter().copied().collect::<BTreeSet<_>>();
        if let Some(shape) = self.direct_match_candidate_positions(fact) {
            let remaining = shape
                .iter()
                .copied()
                .filter(|index| !exact_candidates.contains(index));
            if let CResource::Memory(required_range) = fact.resource() {
                let remaining = remaining.collect::<Vec<_>>();
                candidates.extend(remaining.iter().copied().filter(|index| {
                    self.facts[*index].memory_range().is_some_and(|available| {
                        crate::kernel::assumptions::pointers_equal_ignoring_memories(
                            available.base(),
                            required_range.base(),
                        )
                    })
                }));
                candidates.extend(remaining.into_iter().filter(|index| {
                    !self.facts[*index].memory_range().is_some_and(|available| {
                        crate::kernel::assumptions::pointers_equal_ignoring_memories(
                            available.base(),
                            required_range.base(),
                        )
                    })
                }));
            } else {
                candidates.extend(remaining);
            }
        }
        for index in candidates {
            crate::instrumentation::record_deterministic_work(1);
            // Exact representation is the common path and needs no algebraic
            // decomposition. In particular, splitting an exactly matching
            // symbolic memory range can require arithmetic facts that are
            // irrelevant to consuming the range itself.
            if self.facts[index] == *fact {
                if fact.is_view() {
                    return true;
                }
                self.facts_mut().remove(index);
                return true;
            }
            let available = &self.facts[index];
            let Some(consumption) = algebra.consume(available, fact, assumptions) else {
                continue;
            };
            if let ResourceFactConsumption::Replace(residual) = consumption {
                self.facts_mut().remove(index);
                self.facts_mut().extend(residual);
            }
            return true;
        }
        false
    }

    pub(in crate::kernel) fn normalized(mut self, assumptions: &Assumptions) -> Self {
        let mut slots = self.facts.iter().cloned().map(Some).collect::<Vec<_>>();
        let mut index = ResourceNormalizationIndex::default();
        for (position, fact) in self.facts.iter().enumerate() {
            index.insert(position, fact);
        }
        let mut i = 0;
        while i < slots.len() {
            let Some(fact) = slots[i].clone() else {
                i += 1;
                continue;
            };
            let mut changed = false;
            for j in index.candidates_after(i, &fact) {
                crate::instrumentation::record_deterministic_work(1);
                let Some(right) = slots[j].as_ref() else {
                    continue;
                };
                if let Some(merged) = normalize_resource_fact_pair(&fact, right, assumptions) {
                    index.remove(i, &fact);
                    index.remove(j, right);
                    slots[j] = None;
                    slots[i] = Some(merged.clone());
                    index.insert(i, &merged);
                    changed = true;
                    break;
                }
            }
            if !changed {
                i += 1;
            }
        }
        self.facts = std::sync::Arc::new(slots.into_iter().flatten().collect());
        self.index = std::sync::Arc::new(std::sync::OnceLock::new());
        self
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum ResourceNormalizationKey {
    Resource(CResource),
    ExactShape(ResourceFamily, String, usize),
    MemoryStart(PointerBlock, bool, Bitvector32Term),
    MemoryEnd(PointerBlock, bool, Bitvector32Term),
}

#[derive(Default)]
struct ResourceNormalizationIndex {
    positions: BTreeMap<ResourceNormalizationKey, BTreeSet<usize>>,
}

impl ResourceNormalizationIndex {
    fn keys(fact: &CResourceFact) -> Vec<ResourceNormalizationKey> {
        let mut keys = vec![ResourceNormalizationKey::Resource(fact.resource().clone())];
        match fact.resource() {
            CResource::Memory(range) => {
                keys.push(ResourceNormalizationKey::MemoryStart(
                    range.base().block.clone(),
                    fact.is_own(),
                    range.start().clone(),
                ));
                keys.push(ResourceNormalizationKey::MemoryEnd(
                    range.base().block.clone(),
                    fact.is_own(),
                    range.end().clone(),
                ));
            }
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                keys.push(ResourceNormalizationKey::ExactShape(
                    fact.family(),
                    name.clone(),
                    arguments.len(),
                ));
            }
        }
        keys
    }

    fn insert(&mut self, position: usize, fact: &CResourceFact) {
        for key in Self::keys(fact) {
            self.positions.entry(key).or_default().insert(position);
        }
    }

    fn remove(&mut self, position: usize, fact: &CResourceFact) {
        for key in Self::keys(fact) {
            if let Some(positions) = self.positions.get_mut(&key) {
                positions.remove(&position);
            }
        }
    }

    fn candidates_after(&self, position: usize, fact: &CResourceFact) -> Vec<usize> {
        let mut keys = vec![ResourceNormalizationKey::Resource(fact.resource().clone())];
        match fact.resource() {
            CResource::Memory(range) => {
                keys.push(ResourceNormalizationKey::MemoryEnd(
                    range.base().block.clone(),
                    fact.is_own(),
                    range.start().clone(),
                ));
                keys.push(ResourceNormalizationKey::MemoryStart(
                    range.base().block.clone(),
                    fact.is_own(),
                    range.end().clone(),
                ));
            }
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                keys.push(ResourceNormalizationKey::ExactShape(
                    fact.family(),
                    name.clone(),
                    arguments.len(),
                ));
            }
        }
        let mut candidates = BTreeSet::new();
        for key in keys {
            if let Some(positions) = self.positions.get(&key) {
                candidates.extend(positions.range((position + 1)..).copied());
            }
        }
        candidates.into_iter().collect()
    }
}

fn resource_family_algebra(family: ResourceFamily) -> &'static dyn ResourceFamilyAlgebra {
    let algebra: &'static dyn ResourceFamilyAlgebra = match family {
        ResourceFamily::Memory => &MEMORY_RESOURCE_ALGEBRA,
        ResourceFamily::Composite => &COMPOSITE_RESOURCE_ALGEBRA,
        ResourceFamily::Token => &TOKEN_RESOURCE_ALGEBRA,
    };
    debug_assert_eq!(algebra.family(), family);
    algebra
}

fn resource_fact_entails(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &Assumptions,
) -> bool {
    available.family() == required.family()
        && resource_family_algebra(available.family()).entails(available, required, assumptions)
}

fn normalize_resource_fact_pair(
    left: &CResourceFact,
    right: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<CResourceFact> {
    if left.family() != right.family() {
        return None;
    }
    resource_family_algebra(left.family()).normalize_pair(left, right, assumptions)
}

fn memory_resource_fact_entails(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &Assumptions,
) -> bool {
    if available == required {
        return true;
    }
    match (available, required) {
        (_, _) if required.memory_view_range().is_some() => {
            let required = required.memory_view_range().expect("checked above");
            let Some(available) = resource_fact_read_core_range(available) else {
                return false;
            };
            memory_range_covers(&available, required, assumptions)
        }
        (_, _) if required.memory_own_range().is_some() => {
            let Some(available) = available.memory_own_range() else {
                return false;
            };
            let required = required.memory_own_range().expect("checked above");
            memory_range_covers(available, required, assumptions)
        }
        _ => false,
    }
}

fn consume_memory_resource_fact(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<ResourceFactConsumption> {
    if let Some(required) = required.memory_view_range() {
        return resource_fact_read_core_range(available)
            .is_some_and(|available| memory_range_covers(&available, required, assumptions))
            .then_some(ResourceFactConsumption::Preserve);
    }
    if let Some(required) = required.memory_own_range() {
        let available = available.memory_own_range()?;
        if !memory_range_covers(available, required, assumptions) {
            return None;
        }
        return Some(ResourceFactConsumption::Replace(
            split_memory_range(available, required, assumptions)?
                .into_iter()
                .map(CResourceFact::own_memory)
                .collect(),
        ));
    }
    unreachable!("non-memory resource sent to memory resource consumer")
}

fn exact_resources_proven_equal(
    left: &CResource,
    right: &CResource,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            CResource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        )
        | (
            CResource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Token {
                name: right_name,
                arguments: right_arguments,
            },
        ) => {
            left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments)
                    .all(|(left, right)| {
                        c_values_proven_equal_for_memory_resolution(left, right, assumptions)
                    })
        }
        _ => false,
    }
}

fn exact_resource_fact_entails(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &Assumptions,
) -> bool {
    match (available, required) {
        (
            CResourceFact::Own(available, available_quantity),
            CResourceFact::Own(required, required_quantity),
        ) => {
            available_quantity >= required_quantity
                && exact_resources_proven_equal(available, required, assumptions)
        }
        (
            CResourceFact::Own(available, _) | CResourceFact::View(available),
            CResourceFact::View(required),
        ) => exact_resources_proven_equal(available, required, assumptions),
        _ => false,
    }
}

fn consume_exact_resource_fact(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<ResourceFactConsumption> {
    if !exact_resource_fact_entails(available, required, assumptions) {
        return None;
    }
    Some(if required.is_view() {
        ResourceFactConsumption::Preserve
    } else {
        let CResourceFact::Own(available, available_quantity) = available else {
            unreachable!("owned exact requirement entailed by a viewed fact")
        };
        let CResourceFact::Own(_, required_quantity) = required else {
            unreachable!("checked above")
        };
        let residual = available_quantity.get() - required_quantity.get();
        ResourceFactConsumption::Replace(
            NonZeroU32::new(residual)
                .map(|quantity| CResourceFact::Own(available.clone(), quantity))
                .into_iter()
                .collect(),
        )
    })
}

fn combine_exact_resource_facts(
    left: &CResourceFact,
    right: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<CResourceFact> {
    match (left, right) {
        (CResourceFact::Own(left, quantity), CResourceFact::View(right))
        | (CResourceFact::View(right), CResourceFact::Own(left, quantity))
            if exact_resources_proven_equal(left, right, assumptions) =>
        {
            Some(CResourceFact::Own(left.clone(), *quantity))
        }
        (CResourceFact::View(left), CResourceFact::View(right))
            if exact_resources_proven_equal(left, right, assumptions) =>
        {
            Some(CResourceFact::View(left.clone()))
        }
        _ => None,
    }
}

fn access_mode_core(resource: &CResourceFact) -> Option<CResourceFact> {
    match resource {
        CResourceFact::Own(resource, _) | CResourceFact::View(resource) => {
            Some(CResourceFact::View(resource.clone()))
        }
    }
}

fn same_family_separate_facts(facts: &[&CResourceFact]) -> Vec<Proposition> {
    let owned = facts
        .iter()
        .filter_map(|fact| fact.owned_resource())
        .collect::<Vec<_>>();
    let mut propositions = Vec::new();
    for i in 0..owned.len() {
        for right in &owned[i + 1..] {
            if resources_structurally_separate(owned[i], right) {
                continue;
            }
            propositions.push(Proposition::CResourceSeparate {
                left: owned[i].clone(),
                right: (*right).clone(),
            });
        }
    }
    propositions
}

fn memory_separate_facts(facts: &[&CResourceFact]) -> Vec<Proposition> {
    let mut by_block = BTreeMap::<PointerBlock, Vec<&CResource>>::new();
    for resource in facts.iter().filter_map(|fact| fact.owned_resource()) {
        let CResource::Memory(range) = resource else {
            continue;
        };
        crate::instrumentation::record_deterministic_work(1);
        by_block
            .entry(range.base().block.clone())
            .or_default()
            .push(resource);
    }
    let mut propositions = Vec::new();
    for owned in by_block.values() {
        let one_concrete_base = owned
            .first()
            .and_then(|resource| match resource {
                CResource::Memory(range) => Some(range.base()),
                _ => None,
            })
            .is_some_and(|base| {
                owned.iter().all(|resource| match resource {
                    CResource::Memory(range) => {
                        range.base() == base
                            && range.start().as_const().is_some()
                            && range.end().as_const().is_some()
                    }
                    _ => false,
                })
            });
        if one_concrete_base {
            // Validity already established that these ordered intervals do
            // not overlap, and the kernel proves their concrete separation
            // without a premise. No pair traversal or output is needed.
            continue;
        }
        for i in 0..owned.len() {
            for right in &owned[i + 1..] {
                crate::instrumentation::record_deterministic_work(1);
                if resources_structurally_separate(owned[i], right) {
                    continue;
                }
                propositions.push(Proposition::CResourceSeparate {
                    left: owned[i].clone(),
                    right: (*right).clone(),
                });
            }
        }
    }
    propositions
}

/// Separation cases whose proof depends only on the resource constructors,
/// not on ambient facts or the composition that happened to contain them.
pub(in crate::kernel) fn resources_structurally_separate(
    left: &CResource,
    right: &CResource,
) -> bool {
    match (left, right) {
        (CResource::Memory(left), CResource::Memory(right)) => {
            left.base().blocks_proven_distinct(right.base())
                || left.base() == right.base()
                    && matches!(
                        (
                            signed_bitvector_constant(left.start()),
                            signed_bitvector_constant(left.end()),
                            signed_bitvector_constant(right.start()),
                            signed_bitvector_constant(right.end()),
                        ),
                        (Some(left_start), Some(left_end), Some(right_start), Some(right_end))
                            if left_end <= right_start || right_end <= left_start
                    )
        }
        _ => false,
    }
}

impl ResourceFamilyAlgebra for MemoryResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::Memory
    }

    fn pair_validity_error(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &Assumptions,
    ) -> Option<ResourceContextValidityError> {
        let (Some(left), Some(right)) = (left.memory_own_range(), right.memory_own_range()) else {
            return None;
        };
        memory_ranges_proven_overlapping(left, right, assumptions).then(|| {
            ResourceContextValidityError::OverlappingWriteResources {
                left: left.clone(),
                right: right.clone(),
            }
        })
    }

    fn entails(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &Assumptions,
    ) -> bool {
        memory_resource_fact_entails(available, required, assumptions)
    }

    fn consume(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &Assumptions,
    ) -> Option<ResourceFactConsumption> {
        consume_memory_resource_fact(available, required, assumptions)
    }

    fn normalize_pair(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &Assumptions,
    ) -> Option<CResourceFact> {
        combine_memory_resource_facts(left, right, assumptions)
    }

    fn core(&self, fact: &CResourceFact) -> Option<CResourceFact> {
        access_mode_core(fact)
    }

    fn observable_facts(
        &self,
        facts: &[&CResourceFact],
        _assumptions: &Assumptions,
    ) -> Vec<Proposition> {
        memory_separate_facts(facts)
    }
}

macro_rules! impl_exact_resource_algebra {
    ($algebra:ty, $family:expr) => {
        impl ResourceFamilyAlgebra for $algebra {
            fn family(&self) -> ResourceFamily {
                $family
            }

            fn pair_validity_error(
                &self,
                _left: &CResourceFact,
                _right: &CResourceFact,
                _assumptions: &Assumptions,
            ) -> Option<ResourceContextValidityError> {
                None
            }

            fn entails(
                &self,
                available: &CResourceFact,
                required: &CResourceFact,
                assumptions: &Assumptions,
            ) -> bool {
                exact_resource_fact_entails(available, required, assumptions)
            }

            fn consume(
                &self,
                available: &CResourceFact,
                required: &CResourceFact,
                assumptions: &Assumptions,
            ) -> Option<ResourceFactConsumption> {
                consume_exact_resource_fact(available, required, assumptions)
            }

            fn normalize_pair(
                &self,
                left: &CResourceFact,
                right: &CResourceFact,
                assumptions: &Assumptions,
            ) -> Option<CResourceFact> {
                match (left, right) {
                    (
                        CResourceFact::Own(left, left_quantity),
                        CResourceFact::Own(right, right_quantity),
                    ) if exact_resources_proven_equal(left, right, assumptions) => left_quantity
                        .get()
                        .checked_add(right_quantity.get())
                        .and_then(NonZeroU32::new)
                        .map(|quantity| CResourceFact::Own(left.clone(), quantity)),
                    _ => combine_exact_resource_facts(left, right, assumptions),
                }
            }

            fn core(&self, fact: &CResourceFact) -> Option<CResourceFact> {
                access_mode_core(fact)
            }

            fn observable_facts(
                &self,
                facts: &[&CResourceFact],
                _assumptions: &Assumptions,
            ) -> Vec<Proposition> {
                same_family_separate_facts(facts)
            }
        }
    };
}

impl_exact_resource_algebra!(TokenResourceAlgebra, ResourceFamily::Token);
impl_exact_resource_algebra!(CompositeResourceAlgebra, ResourceFamily::Composite);

fn resource_fact_read_core_range(resource: &CResourceFact) -> Option<CMemoryRange> {
    match resource.core()? {
        CResourceFact::View(CResource::Memory(range)) => Some(range),
        CResourceFact::View(CResource::Composite { .. } | CResource::Token { .. })
        | CResourceFact::Own(..) => None,
    }
}

fn memory_resource_fact_permits_read(
    resource: &CResourceFact,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &Assumptions,
) -> bool {
    resource_fact_read_core_range(resource).is_some_and(|range| {
        assumptions.pointer_access_in_range(
            pointer,
            byte_width,
            range.base(),
            range.start(),
            range.end(),
        )
    })
}

fn memory_resource_fact_permits_write(
    resource: &CResourceFact,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &Assumptions,
) -> bool {
    match resource {
        CResourceFact::Own(CResource::Memory(range), _) => assumptions.pointer_access_in_range(
            pointer,
            byte_width,
            range.base(),
            range.start(),
            range.end(),
        ),
        CResourceFact::Own(CResource::Composite { .. } | CResource::Token { .. }, _)
        | CResourceFact::View(_) => false,
    }
}

fn pointer_has_structural_range_base(pointer: &Pointer, base: &Pointer) -> bool {
    if pointer.block != base.block {
        return false;
    }
    if crate::kernel::assumptions::pointers_equal_ignoring_memories(pointer, base) {
        return true;
    }
    matches!(
        &pointer.offset,
        PointerOffsetTerm::Add(left, right)
            if crate::kernel::assumptions::pointers_equal_ignoring_memories(
                &Pointer {
                    block: pointer.block.clone(),
                    offset: left.as_ref().clone(),
                },
                base,
            ) || crate::kernel::assumptions::pointers_equal_ignoring_memories(
                &Pointer {
                    block: pointer.block.clone(),
                    offset: right.as_ref().clone(),
                },
                base,
            )
    )
}

/// Range endpoints compare like ordinary terms, and additionally two loads
/// of one pointer are equal when the pointed-to cell is provably unchanged
/// between their snapshots — a range spelled through metadata loads then
/// survives writes to unrelated cells.
fn range_endpoint_terms_equal(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    fn loads_bridged(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        assumptions: &Assumptions,
    ) -> bool {
        // The load-unchanged check re-enters separation reasoning, which can
        // re-enter range comparison; guard against unbounded mutual
        // recursion rather than relying on structural depth.
        thread_local! {
            static ENDPOINT_BRIDGE_ACTIVE: std::cell::Cell<bool> =
                const { std::cell::Cell::new(false) };
        }
        if let (
            Bitvector32Term::MemoryLoad(left_memory, left_pointer),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer),
        ) = (left, right)
            && left_pointer == right_pointer
        {
            if ENDPOINT_BRIDGE_ACTIVE.with(std::cell::Cell::get) {
                crate::kernel::assumptions::note_search_truncation();
                return false;
            }
            ENDPOINT_BRIDGE_ACTIVE.with(|active| active.set(true));
            let bridged = crate::kernel::api::c_memory_load_is_unchanged(
                left_memory,
                right_memory,
                left_pointer,
                assumptions,
            ) || crate::kernel::api::c_memory_load_is_unchanged(
                right_memory,
                left_memory,
                left_pointer,
                assumptions,
            );
            ENDPOINT_BRIDGE_ACTIVE.with(|active| active.set(false));
            return bridged;
        }
        false
    }
    if loads_bridged(left, right, assumptions) {
        return true;
    }
    // Structural descent covers the common affine endpoint spellings
    // (base + load, load - base, load * scale).
    let structurally_bridged = match (left, right) {
        (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
        | (
            Bitvector32Term::Subtract(left_a, left_b),
            Bitvector32Term::Subtract(right_a, right_b),
        )
        | (
            Bitvector32Term::Multiply(left_a, left_b),
            Bitvector32Term::Multiply(right_a, right_b),
        ) => {
            range_endpoint_terms_equal(left_a, right_a, assumptions)
                && range_endpoint_terms_equal(left_b, right_b, assumptions)
        }
        _ => false,
    };
    structurally_bridged
        || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
}

/// Pointer bases compare with the same load bridging as range endpoints:
/// two spellings of one loaded base pointer are equal when the loaded cell
/// is provably unchanged between their snapshots.
fn pointer_bases_equal_with_load_bridging(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    left.block == right.block
        && pointer_offsets_equal_with_load_bridging(&left.offset, &right.offset, assumptions)
}

fn pointer_offsets_equal_with_load_bridging(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            pointer_offsets_equal_with_load_bridging(left_a, right_a, assumptions)
                && pointer_offsets_equal_with_load_bridging(left_b, right_b, assumptions)
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && range_endpoint_terms_equal(left_value, right_value, assumptions)
        }
        _ => false,
    }
}

pub(in crate::kernel) fn memory_range_covers(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &Assumptions,
) -> bool {
    if available == required {
        return true;
    }
    if available.base().blocks_proven_distinct(required.base()) {
        return false;
    }
    if crate::instrumentation::measure_operation(
        "kernel",
        "memory range coverage",
        "memory range coverage: explicit separation",
        || {
            assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                available, required,
            )
        },
    ) {
        return false;
    }
    if crate::instrumentation::measure_operation(
        "kernel",
        "memory range coverage",
        "memory range coverage: exact endpoints",
        || {
            (pointers_proven_equal_for_memory_resolution(
                available.base(),
                required.base(),
                assumptions,
            ) || pointer_bases_equal_with_load_bridging(
                available.base(),
                required.base(),
                assumptions,
            )) && range_endpoint_terms_equal(available.start(), required.start(), assumptions)
                && range_endpoint_terms_equal(available.end(), required.end(), assumptions)
        },
    ) {
        return true;
    }
    if let Some(covers) = memory_range_structurally_covers(available, required) {
        return covers;
    }
    if crate::instrumentation::measure_operation(
        "kernel",
        "memory range coverage",
        "memory range coverage: derived containment",
        || {
            crate::kernel::assumptions::memory_range_contained_for_memory_resolution(
                required,
                available,
                assumptions,
            )
        },
    ) {
        return true;
    }
    crate::instrumentation::measure_operation(
        "kernel",
        "memory range coverage",
        "memory range coverage: fact range",
        || {
            assumptions.range_covered_by_fact_range(
                required,
                available.base(),
                available.start(),
                available.end(),
            )
        },
    )
}

fn memory_resource_fact_range(fact: &CResourceFact) -> Option<&CMemoryRange> {
    match fact {
        CResourceFact::Own(CResource::Memory(range), _)
        | CResourceFact::View(CResource::Memory(range)) => Some(range),
        CResourceFact::Own(CResource::Composite { .. } | CResource::Token { .. }, _)
        | CResourceFact::View(CResource::Composite { .. } | CResource::Token { .. }) => None,
    }
}

fn memory_range_structurally_covers(
    available: &CMemoryRange,
    required: &CMemoryRange,
) -> Option<bool> {
    let base_delta = if required.base() == available.base() {
        Bitvector32Term::Constant(0)
    } else {
        required.base().element_index_from_base(available.base())?
    };
    let available_start = available.start().as_const()? as i32;
    let available_end = available.end().as_const()? as i32;
    let required_start =
        Bitvector32Term::add(base_delta.clone(), required.start().clone()).as_const()? as i32;
    let required_end = Bitvector32Term::add(base_delta, required.end().clone()).as_const()? as i32;
    Some(available_start <= required_start && required_end <= available_end)
}

fn memory_ranges_structurally_disjoint(left: &CMemoryRange, right: &CMemoryRange) -> bool {
    if left.base().blocks_proven_distinct(right.base()) {
        return true;
    }
    let Some(base_delta) = right.base().element_index_from_base(left.base()) else {
        return false;
    };
    let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
        left.start().as_const().map(|value| value as i32),
        left.end().as_const().map(|value| value as i32),
        Bitvector32Term::add(base_delta.clone(), right.start().clone())
            .as_const()
            .map(|value| value as i32),
        Bitvector32Term::add(base_delta, right.end().clone())
            .as_const()
            .map(|value| value as i32),
    ) else {
        return false;
    };
    left_end < right_start || right_end < left_start
}

fn split_memory_range(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &Assumptions,
) -> Option<Vec<CMemoryRange>> {
    // Prefer the held range's own start spelling when the required base is
    // provably that address. A merely structural delta can contain an
    // equivalent load from a later memory snapshot; retaining it would create
    // a symbolic zero-length residue when the required range exhausts the
    // beginning of `available`.
    let available_start_pointer = available
        .base()
        .offset_by_int32_elements(available.start().clone());
    let base_delta = if pointers_proven_equal_for_memory_resolution(
        required.base(),
        &available_start_pointer,
        assumptions,
    ) {
        Some(available.start().clone())
    } else {
        required
            .base()
            .element_index_from_base(available.base())
            .or_else(|| {
                pointer_bases_equal_with_load_bridging(
                    required.base(),
                    available.base(),
                    assumptions,
                )
                .then_some(Bitvector32Term::Constant(0))
            })
    }?;
    let required_start = Bitvector32Term::add(base_delta.clone(), required.start().clone());
    let required_end = Bitvector32Term::add(base_delta, required.end().clone());
    let mut residues = Vec::new();
    if !bitvector_terms_proven_equal(available.start(), &required_start, assumptions)
        && !range_endpoint_terms_equal(available.start(), &required_start, assumptions)
    {
        residues.push(CMemoryRange::new(
            available.base().clone(),
            available.start().clone(),
            required_start.clone(),
        ));
    }
    if !bitvector_terms_proven_equal(&required_end, available.end(), assumptions)
        && !range_endpoint_terms_equal(&required_end, available.end(), assumptions)
    {
        residues.push(CMemoryRange::new(
            available.base().clone(),
            required_end,
            available.end().clone(),
        ));
    }
    Some(residues)
}

fn memory_ranges_proven_overlapping(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &Assumptions,
) -> bool {
    if left.base().blocks_proven_distinct(right.base()) {
        return false;
    }
    if assumptions
        .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(left, right)
    {
        return false;
    }
    let Some(base_delta) = right.base().element_index_from_base(left.base()) else {
        return false;
    };
    let right_start = Bitvector32Term::add(base_delta.clone(), right.start().clone());
    let right_end = Bitvector32Term::add(base_delta, right.end().clone());

    assumptions.decide(&ConditionTerm::signed_less_than(
        left.start().clone(),
        right_end,
    )) == Some(true)
        && assumptions.decide(&ConditionTerm::signed_less_than(
            right_start,
            left.end().clone(),
        )) == Some(true)
}

impl CResource {
    pub fn family(&self) -> ResourceFamily {
        match self {
            Self::Memory(_) => ResourceFamily::Memory,
            Self::Composite { .. } => ResourceFamily::Composite,
            Self::Token { .. } => ResourceFamily::Token,
        }
    }
}

impl CResourceFact {
    pub const ALLOCATION_RESOURCE_NAME: &'static str = "allocation";

    pub fn own_memory(range: CMemoryRange) -> Self {
        Self::own(CResource::Memory(range))
    }

    pub fn view_memory(range: CMemoryRange) -> Self {
        Self::View(CResource::Memory(range))
    }

    pub fn own_composite(name: String, arguments: Vec<CValue>) -> Self {
        Self::own(CResource::Composite { name, arguments })
    }

    pub fn view_composite(name: String, arguments: Vec<CValue>) -> Self {
        Self::View(CResource::Composite { name, arguments })
    }

    pub fn own_token(name: String, arguments: Vec<CValue>) -> Self {
        Self::own(CResource::Token { name, arguments })
    }

    pub fn own(resource: CResource) -> Self {
        Self::Own(resource, NonZeroU32::MIN)
    }

    pub fn own_allocation(base: Pointer, bytes: impl Into<Bitvector32Term>) -> Self {
        let bytes = bytes.into();
        Self::own_token(
            Self::ALLOCATION_RESOURCE_NAME.to_string(),
            vec![CValue::Pointer(base), int32(bytes)],
        )
    }

    pub fn allocation(&self) -> Option<(&Pointer, &Bitvector32Term)> {
        let Self::Own(CResource::Token { name, arguments }, _) = self else {
            return None;
        };
        if name != Self::ALLOCATION_RESOURCE_NAME {
            return None;
        }
        let [CValue::Pointer(base), CValue::Int32(bytes)] = arguments.as_slice() else {
            return None;
        };
        Some((base, bytes))
    }

    pub(in crate::kernel) fn may_refer_to_memory_block(&self, block: &PointerBlock) -> bool {
        match self.resource() {
            CResource::Memory(range) => &range.base().block == block,
            CResource::Composite { arguments, .. } => arguments.iter().any(
                |argument| matches!(argument, CValue::Pointer(pointer) if &pointer.block == block),
            ),
            CResource::Token { .. } => false,
        }
    }

    pub(in crate::kernel) fn is_proven_separate_from_allocation(
        &self,
        base: &Pointer,
        bytes: &Bitvector32Term,
        assumptions: &Assumptions,
    ) -> bool {
        let Some(element_count) = crate::kernel::reasoning::int32_element_count_from_bytes(bytes)
        else {
            return false;
        };
        let allocation_memory = CResource::Memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            element_count,
        ));
        assumptions.proves(&Proposition::CResourceSeparate {
            left: allocation_memory,
            right: self.resource().clone(),
        })
    }

    pub fn view_token(name: String, arguments: Vec<CValue>) -> Self {
        Self::View(CResource::Token { name, arguments })
    }

    pub fn resource(&self) -> &CResource {
        match self {
            Self::Own(resource, _) | Self::View(resource) => resource,
        }
    }

    pub fn is_own(&self) -> bool {
        matches!(self, Self::Own(..))
    }

    pub fn is_view(&self) -> bool {
        matches!(self, Self::View(_))
    }

    pub fn family(&self) -> ResourceFamily {
        self.resource().family()
    }

    pub fn core(&self) -> Option<Self> {
        resource_family_algebra(self.family()).core(self)
    }

    pub fn memory_own_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::Own(CResource::Memory(range), _) => Some(range),
            Self::Own(CResource::Composite { .. } | CResource::Token { .. }, _) | Self::View(_) => {
                None
            }
        }
    }

    pub fn memory_view_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::View(CResource::Memory(range)) => Some(range),
            Self::View(CResource::Composite { .. } | CResource::Token { .. }) | Self::Own(..) => {
                None
            }
        }
    }

    pub fn memory_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::Own(CResource::Memory(range), _) | Self::View(CResource::Memory(range)) => {
                Some(range)
            }
            Self::Own(CResource::Composite { .. } | CResource::Token { .. }, _)
            | Self::View(CResource::Composite { .. } | CResource::Token { .. }) => None,
        }
    }

    pub fn owned_resource(&self) -> Option<&CResource> {
        match self {
            Self::Own(resource, _) => Some(resource),
            Self::View(_) => None,
        }
    }

    pub fn owned_quantity(&self) -> Option<u32> {
        match self {
            Self::Own(_, quantity) => Some(quantity.get()),
            Self::View(_) => None,
        }
    }
}

fn combine_memory_resource_facts(
    left: &CResourceFact,
    right: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<CResourceFact> {
    if let (Some(left_range), Some(right_range)) = (
        memory_resource_fact_range(left),
        memory_resource_fact_range(right),
    ) && memory_ranges_structurally_disjoint(left_range, right_range)
    {
        return None;
    }
    match (left, right) {
        _ if memory_resource_fact_entails(left, right, assumptions) => Some(left.clone()),
        _ if memory_resource_fact_entails(right, left, assumptions) => Some(right.clone()),
        (
            CResourceFact::View(CResource::Memory(left)),
            CResourceFact::View(CResource::Memory(right)),
        ) => merge_memory_ranges(left, right, assumptions).map(CResourceFact::view_memory),
        (
            CResourceFact::Own(CResource::Memory(left), _),
            CResourceFact::Own(CResource::Memory(right), _),
        ) => merge_memory_ranges(left, right, assumptions).map(CResourceFact::own_memory),
        _ => None,
    }
}

fn merge_memory_ranges(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &Assumptions,
) -> Option<CMemoryRange> {
    if left.base() != right.base() {
        return None;
    }
    if left.end() == right.start()
        || bitvector_terms_proven_equal(left.end(), right.start(), assumptions)
    {
        return Some(CMemoryRange::new(
            left.base().clone(),
            left.start().clone(),
            right.end().clone(),
        ));
    }
    if right.end() == left.start()
        || bitvector_terms_proven_equal(right.end(), left.start(), assumptions)
    {
        return Some(CMemoryRange::new(
            left.base().clone(),
            right.start().clone(),
            left.end().clone(),
        ));
    }
    None
}

fn bitvector_terms_proven_equal(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    left == right
        || assumptions.decide(&ConditionTerm::equal(left.clone(), right.clone())) == Some(true)
        || assumptions.bitvector_terms_equal_from_facts(left, right)
}
