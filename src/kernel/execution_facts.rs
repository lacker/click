//! Ordered execution evidence with persistent storage across path forks.
use super::{ConditionTerm, ExecutionPureFact, Proposition};
use std::sync::Arc;

#[cfg(test)]
thread_local! {
    static FACT_READS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn take_fact_reads() -> usize {
    FACT_READS.with(|reads| reads.replace(0))
}

type FactVector = imbl::Vector<Arc<ExecutionPureFact>>;
type BlockIter<'a> = imbl::vector::Iter<'a, FactBlock, imbl::shared_ptr::DefaultSharedPtr>;
type BorrowedFacts<'a> = Box<dyn DoubleEndedIterator<Item = &'a ExecutionPureFact> + 'a>;

/// The order used by PureFactContext::pure_facts: conditions, then propositions.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum ContextFactKey {
    Condition(ConditionTerm),
    Proposition(Proposition),
}
pub(super) type ContextFacts = imbl::OrdMap<ContextFactKey, Arc<ExecutionPureFact>>;

#[derive(Clone, Debug)]
enum FactBlock {
    Facts(Arc<FactVector>),
    Context {
        facts: ContextFacts,
        // The exact ordered prefix, retained rather than copied into an
        // exclusion array. This is publication metadata, not proof authority.
        excluded: Arc<ExecutionFacts>,
    },
}
impl FactBlock {
    fn iter(&self) -> BorrowedFacts<'_> {
        match self {
            Self::Facts(facts) => Box::new(facts.iter().map(Arc::as_ref)),
            Self::Context { facts, excluded } => Box::new(
                facts
                    .iter()
                    .map(|(_, fact)| fact.as_ref())
                    .filter(|fact| !excluded.contains_proposition(fact.proposition())),
            ),
        }
    }
}

/// An ordered fact stream whose forks share unchanged chunks and fact objects.
/// Checked context publications retain their persistent ordered map as a block;
/// they do not copy one array of all context facts into every returned path.
#[derive(Clone, Debug, Default)]
pub struct ExecutionFacts {
    data: Arc<ExecutionFactsData>,
}
#[derive(Clone, Debug, Default)]
struct ExecutionFactsData {
    blocks: imbl::Vector<FactBlock>,
    propositions: imbl::OrdSet<Arc<Proposition>>,
    exact: imbl::HashSet<Arc<ExecutionPureFact>>,
    exact_invalid: bool,
    len: usize,
    propositions_invalid: bool,
    // Every fact of this projection is present in the stream. Append-only
    // publications extend this checkpoint by persistent-map differences.
    covered_context: Option<ContextFacts>,
}
impl ExecutionFacts {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.data.len
    }
    pub fn is_empty(&self) -> bool {
        self.data.len == 0
    }

    /// Logical read equations are checked consequences of selecting a value,
    /// not additional conditions on a pure expression or its branch.
    pub(in crate::kernel) fn has_path_conditions(&self) -> bool {
        self.iter().any(|fact| !fact.is_logical_read_equation())
    }
    pub fn iter(&self) -> ExecutionFactsIter<'_> {
        ExecutionFactsIter {
            blocks: self.data.blocks.iter(),
            front: None,
            back: None,
            remaining: self.data.len,
        }
    }
    pub fn contains(&self, fact: &ExecutionPureFact) -> bool {
        if self.data.exact_invalid {
            return self.iter().any(|item| item == fact);
        }
        if self.data.exact.contains(fact) {
            return true;
        }
        let key = match fact.proposition() {
            Proposition::ConditionIs(condition, _) => ContextFactKey::Condition(condition.clone()),
            proposition => ContextFactKey::Proposition(proposition.clone()),
        };
        self.data.blocks.iter().any(|block| match block {
            FactBlock::Context { facts, excluded } => facts.get(&key).is_some_and(|found| {
                found.as_ref() == fact && !excluded.contains_proposition(fact.proposition())
            }),
            FactBlock::Facts(_) => false,
        })
    }
    pub fn to_vec(&self) -> Vec<ExecutionPureFact> {
        self.iter().cloned().collect()
    }
    pub(crate) fn contains_proposition(&self, proposition: &Proposition) -> bool {
        if self.data.propositions_invalid {
            return self.iter().any(|fact| fact.proposition() == proposition);
        }
        if self.data.propositions.contains(proposition) {
            return true;
        }
        let key = match proposition {
            Proposition::ConditionIs(condition, _) => ContextFactKey::Condition(condition.clone()),
            _ => ContextFactKey::Proposition(proposition.clone()),
        };
        self.data.blocks.iter().any(|block| match block {
            FactBlock::Context { facts, excluded } => facts.get(&key).is_some_and(|fact| {
                fact.proposition() == proposition && !excluded.contains_proposition(proposition)
            }),
            FactBlock::Facts(_) => false,
        })
    }
    fn push_shared(&mut self, fact: Arc<ExecutionPureFact>) {
        let data = Arc::make_mut(&mut self.data);
        data.propositions
            .insert(Arc::new(fact.proposition().clone()));
        data.exact.insert(fact.clone());
        if let Some(FactBlock::Facts(facts)) = data.blocks.back_mut() {
            Arc::make_mut(facts).push_back(fact);
        } else {
            data.blocks
                .push_back(FactBlock::Facts(Arc::new(imbl::vector![fact])));
        }
        data.len += 1;
    }
    pub(crate) fn push(&mut self, fact: ExecutionPureFact) {
        self.push_shared(Arc::new(fact));
    }
    pub(crate) fn append(&mut self, other: &mut Self) {
        if other.is_empty() {
            return;
        }
        let data = Arc::make_mut(&mut self.data);
        let other = Arc::make_mut(&mut other.data);
        data.len += other.len;
        if other.covered_context.is_some() {
            data.covered_context = other.covered_context.take();
        }
        data.propositions_invalid |= other.propositions_invalid;
        data.exact_invalid |= other.exact_invalid;
        data.exact = data.exact.clone().union(std::mem::take(&mut other.exact));
        data.propositions = data
            .propositions
            .clone()
            .union(std::mem::take(&mut other.propositions));
        data.blocks.append(std::mem::take(&mut other.blocks));
        other.len = 0;
    }
    pub(crate) fn extend_shared(&mut self, other: &Self) {
        self.append(&mut other.clone());
    }
    pub(super) fn append_context(&mut self, facts: &ContextFacts) {
        let count = match &self.data.covered_context {
            Some(previous) => previous
                .diff(facts)
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                .filter_map(|change| match change {
                    imbl::ordmap::DiffItem::Add(_, fact)
                    | imbl::ordmap::DiffItem::Update { new: (_, fact), .. } => Some(fact),
                    imbl::ordmap::DiffItem::Remove(..) => None,
                })
                .filter(|fact| !self.contains_proposition(fact.proposition()))
                .count(),
            None => facts
                .iter()
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                .filter(|(_, fact)| !self.contains_proposition(fact.proposition()))
                .count(),
        };
        let excluded = (count != 0).then(|| Arc::new(self.clone()));
        let data = Arc::make_mut(&mut self.data);
        data.covered_context = Some(facts.clone());
        if let Some(excluded) = excluded {
            data.blocks.push_back(FactBlock::Context {
                facts: facts.clone(),
                excluded,
            });
            data.len += count;
        }
    }

    /// Facts missing from an exact checked context. Context publications
    /// compare persistent roots rather than enumerating their shared prefix.
    pub(in crate::kernel) fn facts_not_assumed_by<'a>(
        &'a self,
        assumptions: &super::PureFactContext,
    ) -> Vec<&'a ExecutionPureFact> {
        let mut selected = Vec::new();
        for block in &self.data.blocks {
            match block {
                FactBlock::Facts(facts) => selected.extend(
                    facts
                        .iter()
                        .map(Arc::as_ref)
                        .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                        .filter(|fact| !assumptions.contains_assumed_exact(fact.proposition())),
                ),
                FactBlock::Context { facts, excluded } => {
                    for change in assumptions.execution_fact_projection.diff(facts) {
                        crate::instrumentation::record_deterministic_work(1);
                        let fact = match change {
                            imbl::ordmap::DiffItem::Add(_, fact)
                            | imbl::ordmap::DiffItem::Update { new: (_, fact), .. } => {
                                fact.as_ref()
                            }
                            imbl::ordmap::DiffItem::Remove(..) => continue,
                        };
                        if !excluded.contains_proposition(fact.proposition())
                            && !assumptions.contains_assumed_exact(fact.proposition())
                        {
                            selected.push(fact);
                        }
                    }
                }
            }
        }
        selected
    }

    /// Context projections contain plain logical facts; opaque producer
    /// metadata lives only in explicit blocks.
    pub(in crate::kernel) fn producer_facts(&self) -> impl Iterator<Item = &ExecutionPureFact> {
        self.data
            .blocks
            .iter()
            .filter_map(|block| match block {
                FactBlock::Facts(facts) => Some(facts.iter().map(Arc::as_ref)),
                FactBlock::Context { .. } => None,
            })
            .flatten()
    }
    pub(crate) fn filtered(&self, predicate: impl Fn(&ExecutionPureFact) -> bool) -> Self {
        if self.iter().all(&predicate) {
            return self.clone();
        }
        let mut filtered = Self::new();
        // Keep each unchanged block, including context maps, by identity.
        // Partial producer blocks retain their original fact objects.
        let data = Arc::make_mut(&mut filtered.data);
        data.propositions_invalid = true;
        for block in &self.data.blocks {
            let count = block.iter().filter(|fact| predicate(fact)).count();
            if count == 0 {
                continue;
            }
            if block.iter().all(&predicate) {
                data.blocks.push_back(block.clone());
                data.len += count;
            } else {
                let entries = match block {
                    FactBlock::Facts(facts) => facts
                        .iter()
                        .filter(|fact| predicate(fact))
                        .cloned()
                        .collect(),
                    FactBlock::Context { facts, excluded } => facts
                        .iter()
                        .filter(|(_, fact)| {
                            predicate(fact) && !excluded.contains_proposition(fact.proposition())
                        })
                        .map(|(_, fact)| fact.clone())
                        .collect(),
                };
                data.blocks.push_back(FactBlock::Facts(Arc::new(entries)));
                data.len += count;
            }
        }
        data.exact = explicit_fact_index(&data.blocks);
        filtered
    }
    /// Retain selected occurrences, not selected object addresses: the same
    /// shared fact can occur more than once in a producer stream.
    pub(crate) fn selected(&self, indices: &[usize]) -> Self {
        debug_assert!(indices.windows(2).all(|pair| pair[0] < pair[1]));
        debug_assert!(indices.last().is_none_or(|index| *index < self.len()));
        if indices.len() == self.len() {
            return self.clone();
        }
        let mut result = Self::new();
        let data = Arc::make_mut(&mut result.data);
        data.propositions_invalid = true;
        data.len = indices.len();
        let mut start = 0;
        let mut selected_start = 0;
        for block in &self.data.blocks {
            let end = start + block.iter().count();
            let selected_end = indices.partition_point(|index| *index < end);
            let selected = &indices[selected_start..selected_end];
            if !selected.is_empty() {
                if selected.len() == end - start {
                    data.blocks.push_back(block.clone());
                } else {
                    let entries: Box<dyn Iterator<Item = &Arc<ExecutionPureFact>> + '_> =
                        match block {
                            FactBlock::Facts(facts) => Box::new(facts.iter()),
                            FactBlock::Context { facts, excluded } => {
                                Box::new(facts.iter().map(|(_, fact)| fact).filter(|fact| {
                                    !excluded.contains_proposition(fact.proposition())
                                }))
                            }
                        };
                    let facts = entries
                        .enumerate()
                        .filter(|(index, _)| selected.binary_search(&(start + index)).is_ok())
                        .map(|(_, fact)| fact.clone())
                        .collect();
                    data.blocks.push_back(FactBlock::Facts(Arc::new(facts)));
                }
            }
            selected_start = selected_end;
            start = end;
        }
        data.exact = explicit_fact_index(&data.blocks);
        result
    }
    pub(crate) fn retain(&mut self, predicate: impl Fn(&ExecutionPureFact) -> bool) {
        *self = self.filtered(predicate);
    }
    // Mutating producer metadata is explicit: make only the selected fact
    // unique. A context block is materialized only if a caller edits it.
    fn make_explicit(&mut self) {
        if self.data.blocks.len() == 1
            && matches!(self.data.blocks.front(), Some(FactBlock::Facts(_)))
        {
            return;
        }
        let mut facts = FactVector::new();
        for block in &self.data.blocks {
            match block {
                FactBlock::Facts(entries) => facts.append((**entries).clone()),
                FactBlock::Context {
                    facts: entries,
                    excluded,
                } => facts.extend(
                    entries
                        .iter()
                        .filter(|(_, fact)| !excluded.contains_proposition(fact.proposition()))
                        .map(|(_, fact)| fact.clone()),
                ),
            }
        }
        let data = Arc::make_mut(&mut self.data);
        data.blocks = imbl::vector![FactBlock::Facts(Arc::new(facts))];
        data.propositions_invalid = true;
        data.exact_invalid = true;
    }
    #[cfg(test)]
    pub(crate) fn pop(&mut self) -> Option<ExecutionPureFact> {
        if self.is_empty() {
            return None;
        }
        self.make_explicit();
        let data = Arc::make_mut(&mut self.data);
        data.len -= 1;
        data.propositions_invalid = true;
        data.exact_invalid = true;
        data.covered_context = None;
        let FactBlock::Facts(facts) = &mut data.blocks[0] else {
            unreachable!()
        };
        Arc::make_mut(facts)
            .pop_back()
            .map(|fact| Arc::try_unwrap(fact).unwrap_or_else(|fact| (*fact).clone()))
    }
    pub(crate) fn get_mut(&mut self, index: usize) -> &mut ExecutionPureFact {
        self.make_explicit();
        let data = Arc::make_mut(&mut self.data);
        data.propositions_invalid = true;
        data.exact_invalid = true;
        data.covered_context = None;
        let FactBlock::Facts(facts) = &mut data.blocks[0] else {
            unreachable!()
        };
        // Copy only the selected object, including its producer metadata.
        Arc::make_mut(&mut Arc::make_mut(facts)[index])
    }
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.data, &other.data)
    }
    pub(crate) fn suffix_since(&self, ancestor: &Self) -> Option<Self> {
        if self.shares_storage_with(ancestor) {
            return Some(Self::new());
        }
        if self.len() < ancestor.len() || !self.iter().zip(ancestor).all(|(a, b)| a == b) {
            return None;
        }
        // This operation publishes the local effect delta, not the complete
        // prefix. Keep its original fact objects.
        let mut suffix = Self::new();
        let mut skip = ancestor.len();
        for block in &self.data.blocks {
            match block {
                FactBlock::Facts(facts) => {
                    for fact in facts.iter() {
                        if skip > 0 {
                            skip -= 1;
                        } else {
                            suffix.push_shared(fact.clone());
                        }
                    }
                }
                FactBlock::Context { .. } => {
                    for fact in block.iter() {
                        if skip > 0 {
                            skip -= 1;
                        } else {
                            suffix.push(fact.clone());
                        }
                    }
                }
            }
        }
        Some(suffix)
    }
}
fn explicit_fact_index(blocks: &imbl::Vector<FactBlock>) -> imbl::HashSet<Arc<ExecutionPureFact>> {
    blocks
        .iter()
        .filter_map(|block| match block {
            FactBlock::Facts(facts) => Some(facts.iter().cloned()),
            FactBlock::Context { .. } => None,
        })
        .flatten()
        .collect()
}

impl From<Vec<ExecutionPureFact>> for ExecutionFacts {
    fn from(facts: Vec<ExecutionPureFact>) -> Self {
        facts.into_iter().collect()
    }
}
impl FromIterator<ExecutionPureFact> for ExecutionFacts {
    fn from_iter<T: IntoIterator<Item = ExecutionPureFact>>(facts: T) -> Self {
        let mut result = Self::new();
        result.extend(facts);
        result
    }
}
impl Extend<ExecutionPureFact> for ExecutionFacts {
    fn extend<T: IntoIterator<Item = ExecutionPureFact>>(&mut self, facts: T) {
        for fact in facts {
            self.push(fact);
        }
    }
}
impl std::ops::Index<usize> for ExecutionFacts {
    type Output = ExecutionPureFact;
    fn index(&self, index: usize) -> &Self::Output {
        self.iter().nth(index).expect("fact index out of bounds")
    }
}
impl PartialEq for ExecutionFacts {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.data, &other.data)
            || (self.data.len == other.data.len && self.iter().eq(other))
    }
}
impl Eq for ExecutionFacts {}
impl Ord for ExecutionFacts {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other)
    }
}
impl PartialOrd for ExecutionFacts {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl PartialEq<&ExecutionFacts> for ExecutionFacts {
    fn eq(&self, other: &&ExecutionFacts) -> bool {
        self == *other
    }
}
impl PartialEq<Vec<ExecutionPureFact>> for ExecutionFacts {
    fn eq(&self, other: &Vec<ExecutionPureFact>) -> bool {
        self.iter().eq(other.iter())
    }
}

/// Borrowed insertion-order traversal without a flat fact array.
pub struct ExecutionFactsIter<'a> {
    blocks: BlockIter<'a>,
    front: Option<BorrowedFacts<'a>>,
    back: Option<BorrowedFacts<'a>>,
    remaining: usize,
}
impl<'a> Iterator for ExecutionFactsIter<'a> {
    type Item = &'a ExecutionPureFact;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(fact) = self.front.as_mut().and_then(|iter| iter.next()) {
                self.remaining -= 1;
                #[cfg(test)]
                FACT_READS.with(|reads| reads.set(reads.get() + 1));
                return Some(fact);
            }
            self.front = None;
            if let Some(block) = self.blocks.next() {
                self.front = Some(block.iter());
                continue;
            }
            let fact = self.back.as_mut().and_then(|iter| iter.next());
            if fact.is_some() {
                self.remaining -= 1;
                #[cfg(test)]
                FACT_READS.with(|reads| reads.set(reads.get() + 1));
            }
            return fact;
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}
impl DoubleEndedIterator for ExecutionFactsIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(fact) = self.back.as_mut().and_then(|iter| iter.next_back()) {
                self.remaining -= 1;
                #[cfg(test)]
                FACT_READS.with(|reads| reads.set(reads.get() + 1));
                return Some(fact);
            }
            self.back = None;
            if let Some(block) = self.blocks.next_back() {
                self.back = Some(block.iter());
                continue;
            }
            let fact = self.front.as_mut().and_then(|iter| iter.next_back());
            if fact.is_some() {
                self.remaining -= 1;
                #[cfg(test)]
                FACT_READS.with(|reads| reads.set(reads.get() + 1));
            }
            return fact;
        }
    }
}
impl ExactSizeIterator for ExecutionFactsIter<'_> {}
impl<'a> IntoIterator for &'a ExecutionFacts {
    type Item = &'a ExecutionPureFact;
    type IntoIter = ExecutionFactsIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl IntoIterator for ExecutionFacts {
    type Item = ExecutionPureFact;
    type IntoIter = std::vec::IntoIter<ExecutionPureFact>;
    fn into_iter(self) -> Self::IntoIter {
        self.to_vec().into_iter()
    }
}

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::ExecutionFacts {}
    impl Sealed for [super::ExecutionPureFact] {}
    impl Sealed for Vec<super::ExecutionPureFact> {}
    impl<const N: usize> Sealed for [super::ExecutionPureFact; N] {}
    impl<T: super::ExecutionFactSource + ?Sized> Sealed for &T {}
    impl<T: super::ExecutionFactSource + ?Sized> Sealed for std::sync::Arc<T> {}
}

/// Read evidence without requiring contiguous storage. Only the kernel's
/// storage adapters implement this trait, keeping borrowed traversal and
/// persistent snapshots consistent.
pub trait ExecutionFactSource: sealed::Sealed {
    fn fact_iter(&self) -> impl DoubleEndedIterator<Item = &ExecutionPureFact> + ExactSizeIterator;
    fn persistent_facts(&self) -> ExecutionFacts {
        self.fact_iter().cloned().collect()
    }
    fn len(&self) -> usize {
        self.fact_iter().len()
    }
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
impl ExecutionFactSource for ExecutionFacts {
    fn fact_iter(&self) -> impl DoubleEndedIterator<Item = &ExecutionPureFact> + ExactSizeIterator {
        self.iter()
    }
    fn persistent_facts(&self) -> ExecutionFacts {
        self.clone()
    }
}
impl ExecutionFactSource for [ExecutionPureFact] {
    fn fact_iter(&self) -> impl DoubleEndedIterator<Item = &ExecutionPureFact> + ExactSizeIterator {
        self.iter()
    }
}
impl ExecutionFactSource for Vec<ExecutionPureFact> {
    fn fact_iter(&self) -> impl DoubleEndedIterator<Item = &ExecutionPureFact> + ExactSizeIterator {
        self.as_slice().iter()
    }
}
impl<const N: usize> ExecutionFactSource for [ExecutionPureFact; N] {
    fn fact_iter(&self) -> impl DoubleEndedIterator<Item = &ExecutionPureFact> + ExactSizeIterator {
        self.as_slice().iter()
    }
}
impl<T: ExecutionFactSource + ?Sized> ExecutionFactSource for &T {
    fn fact_iter(&self) -> impl DoubleEndedIterator<Item = &ExecutionPureFact> + ExactSizeIterator {
        (**self).fact_iter()
    }
    fn persistent_facts(&self) -> ExecutionFacts {
        (**self).persistent_facts()
    }
}
impl<T: ExecutionFactSource + ?Sized> ExecutionFactSource for Arc<T> {
    fn fact_iter(&self) -> impl DoubleEndedIterator<Item = &ExecutionPureFact> + ExactSizeIterator {
        (**self).fact_iter()
    }
    fn persistent_facts(&self) -> ExecutionFacts {
        (**self).persistent_facts()
    }
}

impl<const N: usize> PartialEq<[ExecutionPureFact; N]> for ExecutionFacts {
    fn eq(&self, other: &[ExecutionPureFact; N]) -> bool {
        self.iter().eq(other.iter())
    }
}
impl PartialEq<[ExecutionPureFact]> for ExecutionFacts {
    fn eq(&self, other: &[ExecutionPureFact]) -> bool {
        self.iter().eq(other.iter())
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct StorageSample {
    pub(crate) paths: usize,
    pub(crate) logical_facts: usize,
    pub(crate) fact_values: usize,
    pub(crate) vector_chunks: usize,
}
#[cfg(test)]
thread_local! {
    static STORAGE_SAMPLES: std::cell::RefCell<Option<[StorageSample; 2]>> = const { std::cell::RefCell::new(None) };
}
#[cfg(test)]
impl ExecutionFacts {
    pub(crate) fn measure_published_storage<T>(run: impl FnOnce() -> T) -> (T, [StorageSample; 2]) {
        struct Reset;
        impl Drop for Reset {
            fn drop(&mut self) {
                STORAGE_SAMPLES.with(|samples| *samples.borrow_mut() = None);
            }
        }
        STORAGE_SAMPLES.with(|samples| *samples.borrow_mut() = Some([StorageSample::default(); 2]));
        let _reset = Reset;
        let result = run();
        let samples = STORAGE_SAMPLES.with(|samples| samples.borrow().unwrap());
        (result, samples)
    }
    pub(crate) fn record_published_storage<'a>(
        checked: bool,
        paths: usize,
        streams: impl Iterator<Item = &'a Self>,
    ) {
        STORAGE_SAMPLES.with(|samples| {
            let mut samples = samples.borrow_mut();
            let Some(samples) = samples.as_mut() else {
                return;
            };
            let sample = &mut samples[usize::from(checked)];
            if paths < sample.paths {
                return;
            }
            let mut values = std::collections::BTreeSet::new();
            let mut chunks = std::collections::BTreeSet::new();
            let mut excluded = std::collections::BTreeSet::new();
            let mut bytes = 0;
            let mut logical = 0;
            for stream in streams {
                logical += stream.len();
                stream.visit_storage(&mut values, &mut chunks, &mut excluded, &mut bytes);
            }
            let measured = StorageSample {
                paths,
                logical_facts: logical,
                fact_values: values.len(),
                vector_chunks: bytes,
            };
            if paths > sample.paths
                || measured.fact_values > sample.fact_values
                || measured.vector_chunks > sample.vector_chunks
            {
                *sample = measured;
            }
        });
    }
    fn visit_storage(
        &self,
        values: &mut std::collections::BTreeSet<usize>,
        chunks: &mut std::collections::BTreeSet<usize>,
        excluded: &mut std::collections::BTreeSet<usize>,
        bytes: &mut usize,
    ) {
        for chunk in self.data.blocks.leaves() {
            if !chunks.insert(chunk.as_ptr() as usize) {
                continue;
            }
            *bytes += 1;
            for block in chunk {
                match block {
                    FactBlock::Facts(facts) => {
                        for chunk in facts.leaves() {
                            if !chunks.insert(chunk.as_ptr() as usize) {
                                continue;
                            }
                            *bytes += 1;
                            values.extend(chunk.iter().map(|fact| Arc::as_ptr(fact) as usize));
                        }
                    }
                    FactBlock::Context {
                        facts,
                        excluded: prefix,
                    } => {
                        values.extend(facts.iter().map(|(_, fact)| Arc::as_ptr(fact) as usize));
                        if excluded.insert(Arc::as_ptr(prefix) as usize) {
                            prefix.visit_storage(values, chunks, excluded, bytes);
                        }
                    }
                }
            }
        }
    }
}

impl<const N: usize> From<[ExecutionPureFact; N]> for ExecutionFacts {
    fn from(facts: [ExecutionPureFact; N]) -> Self {
        facts.into_iter().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{Bitvector32Term, PureFactContext, Variable};

    fn guard(index: u32, value: bool) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(index as u64)),
                Bitvector32Term::Constant(0),
            ),
            value,
        )
    }

    // Indexed lookups must avoid fact-list walks without conflating producer metadata or occurrences.
    #[test]
    fn exact_membership_keeps_producer_metadata_and_selected_occurrences() {
        for size in [64, 128, 256, 512] {
            let facts: ExecutionFacts = (0..size)
                .map(|index| ExecutionPureFact::new(guard(index, true)))
                .collect();
            take_fact_reads();
            for index in 0..size {
                assert!(facts.contains(&ExecutionPureFact::new(guard(index, true))));
                assert!(!facts.contains(&ExecutionPureFact::certified(guard(index, true))));
            }
            assert_eq!(
                take_fact_reads(),
                0,
                "indexed membership must not scan {size} facts"
            );
            let selected = facts.selected(&[0, size as usize - 1]);
            assert!(selected.contains(&ExecutionPureFact::new(guard(0, true))));
            assert!(!selected.contains(&ExecutionPureFact::new(guard(1, true))));
            let mut edited = selected.clone();
            *edited.get_mut(0) = ExecutionPureFact::certified(guard(0, true));
            take_fact_reads();
            assert!(!edited.contains(&ExecutionPureFact::new(guard(0, true))));
            assert!(
                take_fact_reads() > 0,
                "explicit metadata edits use the ordered fallback"
            );
            assert!(edited.contains(&ExecutionPureFact::certified(guard(0, true))));
            assert!(selected.contains(&ExecutionPureFact::new(guard(0, true))));
        }
    }

    #[test]
    fn fragment_merge_suppresses_repeated_shared_occurrences() {
        let source: ExecutionFacts = [ExecutionPureFact::new(guard(1, true))].into();
        let mut repeated = source.clone();
        repeated.extend_shared(&source);
        assert!(std::ptr::eq(&repeated[0], &repeated[1]));
        let merged = crate::kernel::reasoning::path_facts::merge_facts(
            &ExecutionFacts::new(),
            &repeated,
            &PureFactContext::new(),
        )
        .expect("a repeated guard is redundant, not contradictory");
        assert_eq!(merged.len(), 1);
        assert!(std::ptr::eq(&merged[0], &source[0]));
        for index in [0, 1] {
            let selected = repeated.selected(&[index]);
            assert_eq!(selected.len(), 1);
            assert!(std::ptr::eq(&selected[0], &source[0]));
        }
        let certified: ExecutionFacts = [ExecutionPureFact::certified(guard(1, true))].into();
        let mut repeated = certified.clone();
        repeated.extend_shared(&certified);
        let merged = crate::kernel::reasoning::path_facts::merge_facts(
            &ExecutionFacts::new(),
            &repeated,
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(merged.len(), 1);
        assert!(merged[0].is_certified());
        assert!(std::ptr::eq(&merged[0], &certified[0]));
        let opposite: ExecutionFacts = [ExecutionPureFact::new(guard(1, false))].into();
        assert!(
            crate::kernel::reasoning::path_facts::merge_facts(
                &source,
                &opposite,
                &PureFactContext::new(),
            )
            .is_none()
        );
    }

    #[test]
    fn forks_share_roots_and_isolate_metadata_edits() {
        for size in [4, 64, 1024] {
            let root: ExecutionFacts = (0..size)
                .map(|index| ExecutionPureFact::certified(guard(index, false)))
                .collect();
            let mut fork = root.clone();
            assert!(root.shares_storage_with(&fork));
            fork.push(ExecutionPureFact::new(guard(size, true)));
            assert_eq!(root.len(), size as usize);
            assert!(!root.contains_proposition(&guard(size, true)));
            for (a, b) in root.iter().zip(&fork) {
                assert!(std::ptr::eq(a, b));
            }
            *fork.get_mut(0) = ExecutionPureFact::new(guard(0, true));
            assert!(root[0].is_certified());
            assert!(!fork[0].is_certified());
            assert!(!fork.contains_proposition(&guard(0, false)));
            assert!(fork.contains_proposition(&guard(0, true)));
            for (a, b) in root.iter().skip(1).zip(fork.iter().skip(1)) {
                assert!(std::ptr::eq(a, b));
            }
            assert_ne!(root, fork);
            drop(root);
            assert_eq!(fork.len(), size as usize + 1);
        }
    }

    #[test]
    fn context_blocks_preserve_order_isolation_and_share_fact_objects() {
        for size in [16, 64, 256, 1024] {
            let root = (0..size).fold(PureFactContext::new(), |context, index| {
                context.assume_proposition(guard(index, false))
            });
            let mut root_facts = ExecutionFacts::new();
            root_facts.append_context(&root.execution_fact_projection);
            let expected = root.pure_facts();
            assert_eq!(
                root_facts
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .collect::<Vec<_>>(),
                expected
            );
            let mut forks = Vec::new();
            for arm in 0..4 {
                let context = root.clone().assume_proposition(guard(size + arm, true));
                let mut facts = ExecutionFacts::new();
                facts.append_context(&context.execution_fact_projection);
                assert_eq!(facts.len(), size as usize + 1);
                for (before, after) in root_facts.iter().zip(&facts) {
                    assert!(std::ptr::eq(before, after));
                }
                assert!(!facts.contains_proposition(&guard(size + (arm + 1) % 4, true)));
                forks.push(facts);
            }
            drop(root_facts);
            drop(root);
            assert_eq!(forks[0].len(), size as usize + 1);
            let selected = forks[0].selected(&[1, size as usize]);
            assert_eq!(selected.len(), 2);
            assert!(std::ptr::eq(&selected[0], &forks[0][1]));
            assert!(std::ptr::eq(&selected[1], &forks[0][size as usize]));
            assert!(!selected.contains_proposition(&guard(0, false)));
            // Mixed-direction traversal must neither repeat nor omit a fact.
            let mut iter = forks[0].iter();
            assert_eq!(iter.next().unwrap().proposition(), &guard(0, false));
            assert_eq!(iter.next_back().unwrap().proposition(), &guard(size, true));
            assert_eq!(iter.len(), size as usize - 1);
            assert_eq!(iter.count(), size as usize - 1);
        }
    }

    #[test]
    fn context_projection_tracks_replacements_and_withdrawals() {
        let first = guard(1, true);
        let second = Proposition::Predicate {
            name: "projection_test".into(),
            arguments: vec![],
        };
        let context = PureFactContext::new()
            .assume_proposition(first.clone())
            .assume_proposition(second.clone());
        let changed = context
            .clone()
            .assume_proposition(guard(1, false))
            .without_exact_fact(&second);
        for context in [
            &context,
            &changed,
            &context.with_only_proposition_facts(&[]),
        ] {
            let mut facts = ExecutionFacts::new();
            facts.append_context(&context.execution_fact_projection);
            assert_eq!(
                facts
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .collect::<Vec<_>>(),
                context.pure_facts()
            );
        }
    }

    #[test]
    fn context_checkpoint_is_invalidated_by_edits_and_selection() {
        let context = PureFactContext::new()
            .assume_proposition(guard(1, true))
            .assume_proposition(guard(2, false));
        let mut facts = ExecutionFacts::new();
        facts.append_context(&context.execution_fact_projection);
        let mut selected = facts.selected(&[0]);
        selected.append_context(&context.execution_fact_projection);
        assert_eq!(selected.len(), 2);
        *facts.get_mut(0) = ExecutionPureFact::certified(guard(3, true));
        facts.append_context(&context.execution_fact_projection);
        assert_eq!(facts.len(), 3);
        assert!(facts[0].is_certified());
        assert!(facts.contains_proposition(&guard(1, true)));
        facts.pop();
        facts.append_context(&context.execution_fact_projection);
        assert_eq!(facts.len(), 3);
        let subset = facts.filtered(|fact| fact.proposition() != &guard(2, false));
        let mut subset = subset;
        subset.append_context(&context.execution_fact_projection);
        assert_eq!(subset.len(), 3);
    }
    #[test]
    fn context_publication_deduplicates_by_proposition_and_preserves_metadata() {
        let proposition = guard(1, true);
        let mut facts: ExecutionFacts =
            vec![ExecutionPureFact::certified(proposition.clone())].into();
        let before = facts.clone();
        let context = PureFactContext::new()
            .assume_proposition(proposition.clone())
            .assume_proposition(guard(2, false));
        facts.append_context(&context.execution_fact_projection);
        assert_eq!(facts.len(), 2);
        assert!(facts[0].is_certified());
        assert!(std::ptr::eq(&facts[0], &before[0]));
        assert_eq!(
            facts
                .iter()
                .rev()
                .map(|fact| fact.proposition())
                .collect::<Vec<_>>(),
            vec![&guard(2, false), &proposition]
        );
        assert_eq!(facts.filtered(|fact| fact.is_public()), facts);
    }
}
