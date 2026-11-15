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

#[cfg(test)]
thread_local! {
    static CONTEXT_BLOCK_PROBES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Counts one context block read to answer or index membership.
fn note_context_block_probe() {
    #[cfg(test)]
    CONTEXT_BLOCK_PROBES.with(|probes| probes.set(probes.get() + 1));
}

#[cfg(test)]
fn take_context_block_probes() -> usize {
    CONTEXT_BLOCK_PROBES.with(|probes| probes.replace(0))
}

#[cfg(test)]
thread_local! {
    static INDEXED_FACTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many facts streams have indexed from scratch on this thread, when a
/// lookup first asked for their membership.
#[cfg(test)]
pub(crate) fn indexed_execution_facts() -> usize {
    INDEXED_FACTS.with(std::cell::Cell::get)
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
    // Membership indexes over every block, context blocks included, built
    // when first queried and kept current by later appends once built. A
    // stream published per path and never queried does not index its whole
    // history.
    indexes: std::sync::OnceLock<FactIndexes>,
    len: usize,
    // Every fact of this projection is present in the stream. Append-only
    // publications extend this checkpoint by persistent-map differences.
    covered_context: Option<ContextFacts>,
}
#[derive(Clone, Debug, Default)]
struct FactIndexes {
    exact: imbl::HashSet<Arc<ExecutionPureFact>>,
    propositions: imbl::OrdSet<Arc<Proposition>>,
}

impl FactIndexes {
    fn insert(&mut self, fact: &Arc<ExecutionPureFact>) {
        self.propositions
            .insert(Arc::new(fact.proposition().clone()));
        self.exact.insert(fact.clone());
    }
}

impl ExecutionFacts {
    fn indexes(&self) -> &FactIndexes {
        self.data
            .indexes
            .get_or_init(|| block_fact_indexes(&self.data.blocks))
    }
    pub fn new() -> Self {
        Self::default()
    }
    /// Builds the membership indexes now, so a stream that keeps growing
    /// (a path's case facts) keeps them current through each push and every
    /// fork shares them, rather than each fork indexing its whole history
    /// when first asked.
    pub(crate) fn ensure_indexed(&self) {
        self.indexes();
    }
    /// Drops the membership indexes, for a stream about to be extended by
    /// one whose own are not wanted here: a lookup rebuilds them.
    pub(crate) fn forget_indexes(&mut self) {
        Arc::make_mut(&mut self.data).indexes = std::sync::OnceLock::new();
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
    /// The facts after the first `start`, oldest first. Whole plain blocks
    /// before `start` are passed over by their length, so a long shared
    /// prefix is not read.
    pub(crate) fn facts_from(&self, start: usize) -> Vec<&ExecutionPureFact> {
        let mut skip = start;
        let mut suffix = Vec::new();
        for block in &self.data.blocks {
            match block {
                FactBlock::Facts(facts) if skip >= facts.len() => skip -= facts.len(),
                FactBlock::Facts(facts) => {
                    suffix.extend((skip..facts.len()).map(|index| facts[index].as_ref()));
                    skip = 0;
                }
                FactBlock::Context { .. } => {
                    suffix.extend(block.iter().skip(skip));
                    skip = 0;
                }
            }
        }
        suffix
    }

    /// The fact object at `index` of a stream of plain blocks: identity, not
    /// content, so a stream built from another by cloning and appending is
    /// recognized without comparing facts. `None` past the end or within a
    /// context block.
    pub(in crate::kernel) fn plain_fact_at(&self, index: usize) -> Option<&Arc<ExecutionPureFact>> {
        let mut index = index;
        for block in &self.data.blocks {
            match block {
                FactBlock::Facts(facts) if index < facts.len() => return facts.get(index),
                FactBlock::Facts(facts) => index -= facts.len(),
                FactBlock::Context { .. } => return None,
            }
        }
        None
    }

    pub fn contains(&self, fact: &ExecutionPureFact) -> bool {
        self.indexes().exact.contains(fact)
    }
    pub fn to_vec(&self) -> Vec<ExecutionPureFact> {
        self.iter().cloned().collect()
    }
    pub(crate) fn contains_proposition(&self, proposition: &Proposition) -> bool {
        self.indexes().propositions.contains(proposition)
    }
    fn push_shared(&mut self, fact: Arc<ExecutionPureFact>) {
        let data = Arc::make_mut(&mut self.data);
        if let Some(indexes) = data.indexes.get_mut() {
            indexes.insert(&fact);
        }
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
        // Keep a built index current; an unbuilt one stays unbuilt.
        let appended = self.data.indexes.get().is_some().then(|| {
            let other = other.indexes().clone();
            (other.exact, other.propositions)
        });
        let data = Arc::make_mut(&mut self.data);
        let other = Arc::make_mut(&mut other.data);
        data.len += other.len;
        if other.covered_context.is_some() {
            data.covered_context = other.covered_context.take();
        }
        if let (Some(indexes), Some((exact, propositions))) = (data.indexes.get_mut(), appended) {
            indexes.exact = indexes.exact.clone().union(exact);
            indexes.propositions = indexes.propositions.clone().union(propositions);
        }
        other.indexes = std::sync::OnceLock::new();
        data.blocks.append(std::mem::take(&mut other.blocks));
        other.len = 0;
    }
    pub(crate) fn extend_shared(&mut self, other: &Self) {
        self.append(&mut other.clone());
    }
    /// Publishes the facts of `facts` this stream does not yet hold as one
    /// context block, and files them in the membership indexes. A lookup then
    /// reads the indexes alone instead of probing every earlier context block,
    /// which a step-by-step proof appends one of per statement.
    pub(super) fn append_context(&mut self, facts: &ContextFacts) {
        let fresh: Vec<Arc<ExecutionPureFact>> = match &self.data.covered_context {
            Some(previous) => previous
                .diff(facts)
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                .filter_map(|change| match change {
                    imbl::ordmap::DiffItem::Add(_, fact)
                    | imbl::ordmap::DiffItem::Update { new: (_, fact), .. } => Some(fact),
                    imbl::ordmap::DiffItem::Remove(..) => None,
                })
                .filter(|fact| !self.contains_proposition(fact.proposition()))
                .cloned()
                .collect(),
            None => facts
                .iter()
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                .filter(|(_, fact)| !self.contains_proposition(fact.proposition()))
                .map(|(_, fact)| fact.clone())
                .collect(),
        };
        let excluded = (!fresh.is_empty()).then(|| Arc::new(self.clone()));
        let data = Arc::make_mut(&mut self.data);
        data.covered_context = Some(facts.clone());
        if let Some(excluded) = excluded {
            data.len += fresh.len();
            if let Some(indexes) = data.indexes.get_mut() {
                for fact in &fresh {
                    indexes.insert(fact);
                }
            }
            data.blocks.push_back(FactBlock::Context {
                facts: facts.clone(),
                excluded,
            });
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
        data.indexes = std::sync::OnceLock::new();
    }
    #[cfg(test)]
    pub(crate) fn pop(&mut self) -> Option<ExecutionPureFact> {
        if self.is_empty() {
            return None;
        }
        self.make_explicit();
        let data = Arc::make_mut(&mut self.data);
        data.len -= 1;
        data.indexes = std::sync::OnceLock::new();
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
        data.indexes = std::sync::OnceLock::new();
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
    /// The facts after `ancestor`'s length, for a stream built by cloning
    /// `ancestor` and appending to it: whole plain blocks of the shared prefix
    /// are passed over by their length and the prefix is not compared, so
    /// the work is the suffix's. `None` when the stream is shorter.
    pub(crate) fn appended_since(&self, ancestor: &Self) -> Option<Self> {
        if self.shares_storage_with(ancestor) {
            return Some(Self::new());
        }
        let mut skip = ancestor.len();
        if self.len() < skip {
            return None;
        }
        let mut suffix = Self::new();
        for block in &self.data.blocks {
            match block {
                FactBlock::Facts(facts) if skip >= facts.len() => skip -= facts.len(),
                FactBlock::Facts(facts) => {
                    for index in skip..facts.len() {
                        suffix.push_shared(facts[index].clone());
                    }
                    skip = 0;
                }
                FactBlock::Context { .. } => {
                    for fact in block.iter().skip(skip) {
                        suffix.push(fact.clone());
                    }
                    skip = skip.saturating_sub(block.iter().count());
                }
            }
        }
        Some(suffix)
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
/// The membership indexes of `blocks`: every fact each block yields, a
/// context block's included, and their propositions.
fn block_fact_indexes(blocks: &imbl::Vector<FactBlock>) -> FactIndexes {
    let mut indexes = FactIndexes::default();
    let mut index = |fact: &Arc<ExecutionPureFact>| {
        #[cfg(test)]
        INDEXED_FACTS.with(|count| count.set(count.get() + 1));
        indexes.insert(fact)
    };
    for block in blocks {
        match block {
            FactBlock::Facts(facts) => facts.iter().for_each(&mut index),
            FactBlock::Context { facts, excluded } => {
                note_context_block_probe();
                facts
                    .values()
                    .filter(|fact| !excluded.contains_proposition(fact.proposition()))
                    .for_each(&mut index);
            }
        }
    }
    indexes
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
/// persistent states consistent.
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
    use crate::kernel::{MachineTerm, PureFactContext, Variable};

    fn guard(index: u32, value: bool) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(index as u64)),
                MachineTerm::constant(0),
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
            // An explicit metadata edit drops the index; the next query
            // rebuilds it from the edited facts.
            *edited.get_mut(0) = ExecutionPureFact::certified(guard(0, true));
            assert!(!edited.contains(&ExecutionPureFact::new(guard(0, true))));
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

    // A proof appends one context block per statement; asking whether the
    // stream holds a fact must not probe every earlier block.
    #[test]
    fn membership_reads_no_context_block_of_a_growing_stream() {
        for size in [16, 64, 256] {
            let mut context = PureFactContext::new();
            let mut facts = ExecutionFacts::new();
            for index in 0..size {
                context = context.assume_proposition(guard(index, true));
                facts.append_context(&context.execution_fact_projection);
            }
            assert_eq!(facts.len(), size as usize);
            take_fact_reads();
            take_context_block_probes();
            for index in 0..size {
                assert!(facts.contains_proposition(&guard(index, true)));
                assert!(!facts.contains_proposition(&guard(index, false)));
                assert!(facts.contains(&ExecutionPureFact::new(guard(index, true))));
            }
            assert_eq!(take_fact_reads(), 0, "size {size}");
            assert_eq!(take_context_block_probes(), 0, "size {size}");
            // A filtered or selected stream keeps answering from its indexes,
            // so publishing more context onto it reads no earlier fact.
            let selected = facts.selected(&[0, size as usize - 1]);
            let mut filtered = facts.filtered(|fact| fact.proposition() != &guard(0, true));
            take_fact_reads();
            assert!(selected.contains(&ExecutionPureFact::new(guard(size - 1, true))));
            assert!(!selected.contains(&ExecutionPureFact::new(guard(1, true))));
            assert!(selected.contains_proposition(&guard(0, true)));
            assert!(!filtered.contains_proposition(&guard(0, true)));
            assert!(filtered.contains_proposition(&guard(size - 1, true)));
            assert_eq!(take_fact_reads(), 0, "size {size}");
            let context = context.assume_proposition(guard(size, true));
            filtered.append_context(&context.execution_fact_projection);
            assert_eq!(filtered.len(), size as usize + 1);
            assert_eq!(take_fact_reads(), 0, "size {size}");
        }
    }

    #[test]
    fn context_projection_tracks_replacements() {
        let first = guard(1, true);
        let second = Proposition::Predicate {
            name: "projection_test".into(),
            arguments: vec![],
        };
        let context = PureFactContext::new()
            .assume_proposition(first.clone())
            .assume_proposition(second);
        let changed = context.clone().assume_proposition(guard(1, false));
        for context in [&context, &changed] {
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
