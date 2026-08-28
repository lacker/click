use super::*;
use crate::persistent::PersistentSet;
#[cfg(test)]
use crate::persistent::persistent_node_allocations;
use std::sync::Arc;

/// Identifies the `close_invariants` step of a replayed certificate well
/// enough to emit a `click timing:` line for the work its caller does on its
/// behalf: the same claim-relative indices the checked drivers use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct InvariantCloserStep {
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) statement_index: usize,
}

/// Clone-on-write storage for legacy replay collections.
///
/// This makes a read-only proof-state fork constant time. A legacy mutation
/// still pays for its complete vector and remains an explicit migration
/// target; migrated `Proof` steps avoid that mutable path altogether.
#[derive(Clone)]
pub(super) struct SharedVec<T>(Arc<Vec<T>>);

impl<T> Default for SharedVec<T> {
    fn default() -> Self {
        Self(Arc::new(Vec::new()))
    }
}

impl<T> std::ops::Deref for SharedVec<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<T: Clone> std::ops::DerefMut for SharedVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Arc::make_mut(&mut self.0)
    }
}

impl<T> From<Vec<T>> for SharedVec<T> {
    fn from(value: Vec<T>) -> Self {
        Self(Arc::new(value))
    }
}

impl<'a, T> IntoIterator for &'a SharedVec<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: Clone> SharedVec<T> {
    /// The entries appended after `ancestor`, by length suffix. Effect
    /// histories only append within one execution lineage; the debug build
    /// verifies the shared prefix element-wise, and `None` reports a
    /// shorter-than-ancestor history (not a descendant).
    pub(super) fn suffix_since(&self, ancestor: &Self) -> Option<&[T]>
    where
        T: PartialEq + std::fmt::Debug,
    {
        if self.0.len() < ancestor.0.len() {
            return None;
        }
        debug_assert!(
            self.0[..ancestor.0.len()] == ancestor.0[..],
            "an effect history diverged from its claimed ancestor"
        );
        Some(&self.0[ancestor.0.len()..])
    }

    pub(super) fn into_vec(self) -> Vec<T> {
        Arc::try_unwrap(self.0).unwrap_or_else(|shared| shared.as_ref().clone())
    }

    #[cfg(test)]
    pub(super) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

/// Clone-on-write storage for one legacy replay value.
///
/// `Proof` successors can share replay metadata they do not modify. Legacy
/// code still receives ordinary references through `Deref`, and the first
/// mutation makes the old complete-value copy explicit at that boundary.
#[derive(Clone)]
pub(super) struct SharedValue<T>(Arc<T>);

impl<T: Default> Default for SharedValue<T> {
    fn default() -> Self {
        Self(Arc::new(T::default()))
    }
}

impl<T> std::ops::Deref for SharedValue<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl<T: Clone> std::ops::DerefMut for SharedValue<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Arc::make_mut(&mut self.0)
    }
}

impl<T> From<T> for SharedValue<T> {
    fn from(value: T) -> Self {
        Self(Arc::new(value))
    }
}

impl<T: Clone> SharedValue<T> {
    pub(super) fn into_value(self) -> T {
        Arc::try_unwrap(self.0).unwrap_or_else(|shared| shared.as_ref().clone())
    }

    #[cfg(test)]
    pub(super) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

/// Where a source tactic's expansion is being captured on this path: the
/// deferred capture selected for a post-execution tactic and the C branch
/// choices enclosing it, which the deferred expansion finalizes against
/// after every path has completed.
#[derive(Clone, Default)]
pub(super) struct ExpansionCursor {
    pub(super) deferred_tactic_capture: Option<DeferredTacticCapture>,
    pub(super) deferred_expansion_path_choices: PersistentSequence<SurfacePathChoice>,
}

#[derive(Clone)]
pub(super) struct LoopEffectGoal {
    pub(super) before_state: CState,
    pub(super) check: CLoopEffectCheck,
    pub(super) closed: bool,
}

#[derive(Clone)]
pub(super) struct CaseAssumption {
    pub(super) tactic_index: usize,
    pub(super) condition: ClickProposition,
    pub(super) value: bool,
    pub(super) fact: Option<Proposition>,
    pub(super) at_function_entry: bool,
}

/// An append-only sequence whose forks share their complete history.
///
/// Execution proof branches inherit the enclosing case assumptions and add
/// one local choice. A `Vec` makes that fork copy every enclosing choice even
/// though neither branch can edit them. This parent-linked representation
/// makes both the fork and the local append constant time. Iteration restores
/// insertion order and therefore costs only the number of entries consumed.
#[derive(Clone)]
pub(super) struct PersistentSequence<T> {
    tail: Option<Arc<PersistentSequenceNode<T>>>,
    len: usize,
}

struct PersistentSequenceNode<T> {
    parent: Option<Arc<PersistentSequenceNode<T>>>,
    value: T,
}

impl<T> Default for PersistentSequence<T> {
    fn default() -> Self {
        Self { tail: None, len: 0 }
    }
}

impl<T> Drop for PersistentSequence<T> {
    fn drop(&mut self) {
        // Dropping an `Arc`-owned parent chain recursively drops every unique
        // parent and can exhaust the stack for ordinary large proof histories.
        // Unwrap the unique suffix iteratively. At the first shared ancestor,
        // releasing this sequence's reference is sufficient; whichever owner
        // eventually becomes unique will perform the same iterative cleanup.
        let mut tail = self.tail.take();
        while let Some(node) = tail {
            let Ok(node) = Arc::try_unwrap(node) else {
                break;
            };
            tail = node.parent;
        }
    }
}

impl<T> PersistentSequence<T> {
    pub(super) fn push(&mut self, value: T) {
        self.tail = Some(Arc::new(PersistentSequenceNode {
            parent: self.tail.clone(),
            value,
        }));
        self.len += 1;
    }

    pub(super) fn clear(&mut self) {
        self.tail = None;
        self.len = 0;
    }

    pub(super) fn is_empty(&self) -> bool {
        self.tail.is_none()
    }

    pub(super) fn len(&self) -> usize {
        self.len
    }

    pub(super) fn iter(&self) -> PersistentSequenceIter<'_, T> {
        let mut nodes = Vec::with_capacity(self.len);
        let mut current = self.tail.as_deref();
        while let Some(node) = current {
            nodes.push(&node.value);
            current = node.parent.as_deref();
        }
        nodes.reverse();
        PersistentSequenceIter {
            entries: nodes.into_iter(),
        }
    }

    pub(super) fn to_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.iter().cloned().collect()
    }

    /// The entries appended after `ancestor`'s tail, oldest first.
    ///
    /// Returns `None` when `ancestor` is not a prefix of this sequence by
    /// identity — pointer identity, not structural equality, proves the
    /// shared history — and visits only the appended suffix.
    pub(super) fn suffix_since(&self, ancestor: &Self) -> Option<Vec<T>>
    where
        T: Clone,
    {
        let mut suffix = Vec::with_capacity(self.len.saturating_sub(ancestor.len));
        let mut current = self.tail.clone();
        loop {
            match (&current, &ancestor.tail) {
                (Some(node), Some(ancestor_tail)) if Arc::ptr_eq(node, ancestor_tail) => break,
                (None, None) => break,
                (Some(node), _) => {
                    suffix.push(node.value.clone());
                    current = node.parent.clone();
                }
                (None, Some(_)) => return None,
            }
        }
        suffix.reverse();
        Some(suffix)
    }

    pub(super) fn shares_tail_with(&self, other: &Self) -> bool {
        match (&self.tail, &other.tail) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            (None, None) => true,
            _ => false,
        }
    }
}

impl<T: Clone> PersistentSequence<T> {
    /// Removes the newest entry while preserving any shared ancestor prefix.
    pub(super) fn pop(&mut self) -> Option<T> {
        let tail = self.tail.take()?;
        let value = tail.value.clone();
        self.tail = tail.parent.clone();
        self.len -= 1;
        Some(value)
    }
}

pub(super) struct PersistentSequenceIter<'a, T> {
    entries: std::vec::IntoIter<&'a T>,
}

impl<'a, T> Iterator for PersistentSequenceIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.entries.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.entries.size_hint()
    }
}

impl<T> ExactSizeIterator for PersistentSequenceIter<'_, T> {}

impl<T> DoubleEndedIterator for PersistentSequenceIter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.entries.next_back()
    }
}

impl<'a, T> IntoIterator for &'a PersistentSequence<T> {
    type Item = &'a T;
    type IntoIter = PersistentSequenceIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A deterministic insertion-ordered set with persistent exact membership.
///
/// The sequence preserves certificate/certification order; the AVL index
/// makes exact queries and one local insertion logarithmic. Both roots are
/// shared by a clone, so search forks never copy unrelated entries.
#[derive(Clone)]
pub(super) struct PersistentOrderedSet<T> {
    ordered: PersistentSequence<T>,
    exact: PersistentSet<T>,
}

impl<T> Default for PersistentOrderedSet<T> {
    fn default() -> Self {
        Self {
            ordered: PersistentSequence::default(),
            exact: PersistentSet::default(),
        }
    }
}

impl<T: Clone + Ord> PersistentOrderedSet<T> {
    /// The members inserted after `ancestor`, oldest first, by the same
    /// pointer-identity suffix walk as the underlying sequence. `None` when
    /// `ancestor` is not this set's ancestor.
    pub(super) fn introduced_since(&self, ancestor: &Self) -> Option<Vec<T>> {
        self.ordered.suffix_since(&ancestor.ordered)
    }

    pub(super) fn clear(&mut self) {
        self.ordered.clear();
        self.exact = PersistentSet::default();
    }

    pub(super) fn insert(&mut self, value: T) -> bool {
        if self.exact.contains(&value) {
            return false;
        }
        self.exact = self.exact.with_value(value.clone());
        self.ordered.push(value);
        true
    }

    pub(super) fn contains(&self, value: &T) -> bool {
        self.exact.contains(value)
    }

    pub(super) fn len(&self) -> usize {
        self.ordered.len()
    }

    pub(super) fn iter(&self) -> PersistentSequenceIter<'_, T> {
        self.ordered.iter()
    }

    pub(super) fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }
}

/// Ordered-set iteration follows accepted-step order rather than tree order.
impl<'a, T: Clone + Ord> IntoIterator for &'a PersistentOrderedSet<T> {
    type Item = &'a T;
    type IntoIter = PersistentSequenceIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[derive(Clone, Default)]
pub(super) struct ProofCertificateBuilder {
    pub(super) steps: Vec<SimpleProofStep>,
    pub(super) blocker: Option<String>,
    pub(super) last_step_entry: Option<ProgramPointRef>,
    pub(super) path_choices: Vec<SurfacePathChoice>,
    /// Prevents the planner-metadata wrapper for a statement transition from
    /// re-entering itself while it emits the ordinary surface step.
    pub(super) lowering_planned_transition: bool,
}

/// Deterministically ordered proof facts with an exact-membership index.
///
/// Certificate emission and diagnostics retain insertion order, while a
/// named premise never scans unrelated earlier facts. All mutation stays
/// behind this type so the two views cannot diverge.
#[derive(Clone, Default)]
pub(super) struct ProofFactStore {
    ordered: PersistentSequence<Proposition>,
    exact: PersistentSet<Proposition>,
}

impl ProofFactStore {
    pub(super) fn from_ordered(facts: Vec<Proposition>) -> Self {
        let mut store = Self::default();
        for fact in facts {
            store.insert(fact);
        }
        store
    }

    pub(super) fn insert(&mut self, fact: Proposition) -> bool {
        if self.exact.contains(&fact) {
            return false;
        }
        self.exact = self.exact.with_value(fact.clone());
        self.ordered.push(fact);
        true
    }

    pub(super) fn retain(&mut self, mut keep: impl FnMut(&Proposition) -> bool) {
        let mut retained = Self::default();
        for fact in self.ordered.iter() {
            if keep(fact) {
                retained.insert(fact.clone());
            }
        }
        *self = retained;
    }

    pub(super) fn contains(&self, fact: &Proposition) -> bool {
        self.exact.contains(fact)
    }

    pub(super) fn iter(&self) -> PersistentSequenceIter<'_, Proposition> {
        self.ordered.iter()
    }

    pub(super) fn to_vec(&self) -> Vec<Proposition> {
        self.iter().cloned().collect()
    }

    #[cfg(test)]
    fn shares_persistent_storage_with(&self, other: &Self) -> bool {
        self.ordered.shares_tail_with(&other.ordered) && self.exact.shares_root_with(&other.exact)
    }
}

/// Environments a planning executor needs to construct the [`SimpleProofStep`]
/// for each committed search move at the moment the move is made. Passing
/// `None` runs the executor without surface construction (ordinary replay).
/// The path's surface record: what the constructed certificate's own replay
/// knows at this point. Planning sinks seed from it and write the anchor
/// back; a proof-level case split records its choice here.
#[derive(Clone, Default)]
pub(super) struct SurfaceRecord {
    /// The statement entry the most recent step recorded, which later
    /// snapshot-qualified facts resolve against.
    pub(super) last_step_entry: Option<ProgramPointRef>,
    pub(super) path_choices: Vec<SurfacePathChoice>,
    pub(super) blocker: Option<String>,
    /// The facts the constructed certificate's own replay will have at the
    /// current point. Planning executes with automatically transported facts,
    /// but certificate replay carries only path facts, statement-local
    /// rewrites, and explicit surface transports across each step. Generated
    /// evidence is written against this replay-visible set.
    pub(super) certificate_facts: ProofFactStore,
}

/// One planning call's construction gate: the environments the constructed
/// steps lower against and the sink they are recorded into.
pub(super) struct Construction<'a> {
    pub(super) environments: ConstructionEnvironments<'a>,
    pub(super) sink: &'a mut ProofCertificateBuilder,
}

impl Construction<'_> {
    pub(super) fn reborrow(&mut self) -> Construction<'_> {
        Construction {
            environments: self.environments,
            sink: self.sink,
        }
    }
}

#[derive(Clone, Copy)]
pub(super) struct ConstructionEnvironments<'a> {
    pub(super) predicate_environment: &'a PredicateEnvironment,
    pub(super) click_function_environment: &'a ClickFunctionEnvironment,
}

#[derive(Clone, PartialEq, Eq)]
pub(super) struct DeferredTacticCapture {
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) post_execution_index: usize,
    pub(super) branch_skeleton: Vec<ProofTactic>,
}

impl DeferredTacticCapture {
    /// `post_execution_index` of a capture for a tactic nested in a deferred
    /// `if` arm: it matches by tactic index at whatever drained position.
    pub(super) const NESTED: usize = usize::MAX;
}

pub(in crate::lang::click) fn capture_c0_tactic_expansion(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: ProofSite,
    source_index: usize,
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut capture = ExpansionCapture::for_tactic(site.clone(), source_index);
    let verification =
        verify_c0_sources_with_expansion_capture(click_source, c_sources, &mut capture);
    if let Some(result) = capture.result {
        return result.map_err(ClickError::new);
    }
    match verification {
        Err(error) => {
            match super::tactic_expansion_dependency_context(
                click_source,
                c_sources,
                &site,
                source_index,
            )? {
                Some(context) => Err(ClickError::new(format!(
                    "selected tactic expansion failed while checking {context}: {}",
                    error.message()
                ))),
                None => Err(error),
            }
        }
        Ok(_) => Err(ClickError::new(format!(
            "selected {} proof has no source tactic {source_index}",
            site.description()
        ))),
    }
}

pub(in crate::lang::click) fn capture_c0_proof_site_expansion(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: ProofSite,
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut capture = ExpansionCapture::for_site(site.clone());
    let verification =
        verify_c0_sources_with_expansion_capture(click_source, c_sources, &mut capture);
    if let Some(result) = capture.result {
        return result.map_err(ClickError::new);
    }
    match verification {
        Err(error) => Err(error),
        Ok(_) if matches!(site, ProofSite::LoopPhase { .. }) => {
            // A loop phase nested under an unreachable C path can have no
            // initialization/preservation obligations at all. There is no
            // path certificate to retain, and a synthesized stand-in proof
            // would present itself as verified evidence; report the empty
            // obligation set instead of inventing one.
            Err(ClickError::new(format!(
                "verification retained no certificate for {}: the phase produced no proof obligations (its loop may sit under an unreachable path), so there is no proof to expand",
                site.description()
            )))
        }
        Ok(_) => Err(ClickError::new(format!(
            "verification did not retain a certificate for {}",
            site.description()
        ))),
    }
}

pub(super) fn finish_proof_site_expansion_capture(
    capture: Option<&mut ExpansionCapture>,
    site: &ProofSite,
    certificate: &ProofCertificate,
) {
    let Some(capture) = capture else {
        return;
    };
    if capture.site != *site || capture.source_index.is_some() || capture.result.is_some() {
        return;
    }
    capture.active = true;
    capture.result = Some(Ok(certificate.to_proof_tactics().to_vec()));
}

pub(super) fn record_proof_site_tactic_expansion(
    capture: Option<&mut ExpansionCapture>,
    site: &ProofSite,
    source_index: usize,
    tactics: &[ProofTactic],
) {
    let Some(capture) = capture else {
        return;
    };
    if capture.site != *site || capture.source_index != Some(source_index) {
        return;
    }
    capture.active = true;
    match &mut capture.result {
        None => capture.result = Some(Ok(tactics.to_vec())),
        Some(Ok(existing)) if existing == tactics => {}
        Some(Ok(_)) => {
            capture.result = Some(Err(
                "selected tactic expands differently across proof obligations".to_string(),
            ));
        }
        Some(Err(_)) => {}
    }
}

pub(super) fn selected_tactic_index_for_site(
    capture: Option<&ExpansionCapture>,
    site: &ProofSite,
) -> Option<usize> {
    capture
        .filter(|capture| capture.site == *site)
        .and_then(|capture| capture.source_index)
}

pub(super) fn proof_site_for_claims(
    function_block: &FunctionBlock,
    claims: &[FunctionClaimRef<'_>],
    grouped_contract: bool,
) -> Option<ProofSite> {
    let claim = if grouped_contract {
        CProofClaim::Grouped
    } else {
        match claims {
            [FunctionClaimRef::Ensure(index, _)] => CProofClaim::Ensure(*index),
            [FunctionClaimRef::Effect(index, _)] => CProofClaim::Effect(*index),
            _ => return None,
        }
    };
    Some(ProofSite::FunctionClaim {
        function_name: function_block.signature().name().to_string(),
        claim,
    })
}

/// Marks the capture active when it matches this tactic. The tactic's
/// expansion itself comes from its builder scope; the capture only decides
/// which tactic's scoped result is the requested one.
pub(super) fn begin_tactic_expansion_capture(
    capture: Option<&mut ExpansionCapture>,
    source_index: usize,
    cursor: &ExpansionCursor,
    proof_site: Option<&ProofSite>,
) -> bool {
    let Some(capture) = capture else {
        return false;
    };
    let sibling_branch_capture = capture.active
        && !cursor.deferred_expansion_path_choices.is_empty()
        && capture.source_index == Some(source_index)
        && proof_site == Some(&capture.site);
    if capture.active && !sibling_branch_capture
        || capture.source_index != Some(source_index)
        || proof_site != Some(&capture.site)
    {
        return false;
    }
    capture.active = true;
    true
}

/// `allow_empty` accepts an empty expansion as the exact answer: the selected
/// tactic contributed no surface tactics to the accepted certificate, so the
/// rewrite removes it. Every other caller keeps the empty guard — for them an
/// empty capture means the lowering lost the tactics, not that none exist.
///
/// The first completed capture wins; verification continues normally either
/// way.
pub(super) fn finish_tactic_expansion_capture(
    capture: Option<&mut ExpansionCapture>,
    proof_certificate_builder: &ProofCertificateBuilder,
    allow_empty: bool,
) {
    let Some(capture) = capture else {
        return;
    };
    if capture.result.is_some() {
        return;
    }
    capture.result = Some(match &proof_certificate_builder.blocker {
        Some(blocker) => Err(format!("could not expand selected tactic: {blocker}")),
        None if proof_certificate_builder.steps.is_empty() && !allow_empty => {
            Err("selected tactic produced no standalone surface expansion".to_string())
        }
        None => Ok(
            ProofCertificate::from_steps(proof_certificate_builder.steps.clone())
                .to_proof_tactics(),
        ),
    });
}

pub(super) fn tactic_expansion_capture_is_active(capture: Option<&ExpansionCapture>) -> bool {
    capture.is_some_and(|capture| capture.active)
}

pub(super) fn tactic_expansion_capture_matches(
    capture: Option<&ExpansionCapture>,
    site: Option<&ProofSite>,
    source_index: usize,
) -> bool {
    capture.is_some_and(|capture| {
        capture.active && site == Some(&capture.site) && capture.source_index == Some(source_index)
    })
}

/// Takes one path-local selected-tactic expansion while leaving the capture
/// installed for a sibling execution path. Frontier-local `branch` uses this
/// to collect the certificate produced at one shared source occurrence under
/// each C arm before it emits their logical case split.
pub(super) fn take_path_tactic_expansion_capture(
    capture: Option<&mut ExpansionCapture>,
) -> Result<Vec<ProofTactic>, ClickError> {
    let Some(capture) = capture else {
        return Err(ClickError::new(
            "selected-tactic expansion capture was lost between branch paths",
        ));
    };
    let result = capture.result.take().ok_or_else(|| {
        ClickError::new("selected tactic completed without recording its branch expansion")
    })?;
    capture.active = false;
    result.map_err(ClickError::new)
}

pub(super) fn resume_deferred_tactic_expansion_capture(
    capture: Option<&mut ExpansionCapture>,
    cursor: &ExpansionCursor,
    proof_site: Option<&ProofSite>,
) -> Result<(), ClickError> {
    let Some(deferred) = &cursor.deferred_tactic_capture else {
        return Ok(());
    };
    let Some(capture) = capture else {
        return Err(ClickError::new(
            "selected-tactic expansion capture was lost before deferred finalization",
        ));
    };
    if proof_site != Some(&capture.site) || capture.source_index != Some(deferred.source_index) {
        return Err(ClickError::new(
            "deferred tactic capture no longer matches the selected proof occurrence",
        ));
    }
    capture.active = true;
    Ok(())
}

#[derive(Clone)]
pub(super) struct SurfacePathChoice {
    pub(super) occurrence: usize,
    pub(super) condition: ClickProposition,
    pub(super) value: bool,
    pub(super) tactic_offset: usize,
}

impl ProofCertificateBuilder {
    pub(super) fn push_step(&mut self, step: SimpleProofStep) {
        if self.blocker.is_none() {
            append_surface_step_to_leaves(&mut self.steps, step);
        }
    }

    pub(super) fn push_source_tactic(&mut self, tactic: ProofTactic) {
        if self.blocker.is_some() {
            return;
        }
        match ProofCertificate::from_proof_tactics(std::slice::from_ref(&tactic)) {
            Ok(proof) => {
                let [step] = proof.steps.as_slice() else {
                    unreachable!("one surface tactic must produce one simple proof step")
                };
                self.push_step(step.clone());
            }
            Err(error) => self.block(format!(
                "attempted to record a non-simple surface proof step at {:?}: {:?}",
                error.path(),
                error.tactic_class()
            )),
        }
    }

    pub(super) fn push_have(&mut self, proposition: ClickProposition, proof: SourceProof) {
        let SourceProof::Script(tactics) = proof else {
            self.block("generated `have` proof was not an explicit simple script");
            return;
        };
        match ProofCertificate::from_proof_tactics(&tactics) {
            Ok(proof) => self.push_step(SimpleProofStep::Have {
                proposition,
                proof: Box::new(proof),
            }),
            Err(error) => self.block(format!(
                "generated `have` body was not a simple proof at {:?}: {:?}",
                error.path(),
                error.tactic_class()
            )),
        }
    }

    pub(super) fn block(&mut self, message: impl Into<String>) {
        if self.blocker.is_none() {
            self.blocker = Some(message.into());
            self.steps.clear();
            self.path_choices.clear();
        }
    }
}

pub(super) fn record_post_execution_surface_tactic(
    surface_recorded: bool,
    path_tactics: &mut Vec<ProofTactic>,
    capture_tactics: &mut Vec<ProofTactic>,
    deferred_capture: Option<&DeferredTacticCapture>,
    post_execution_index: usize,
    tactic_index: usize,
    tactic: ProofTactic,
) {
    if surface_recorded {
        return;
    }
    if deferred_capture.is_some_and(|capture| {
        capture.tactic_index == tactic_index
            && (capture.post_execution_index == post_execution_index
                || capture.post_execution_index == DeferredTacticCapture::NESTED)
    }) {
        capture_tactics.push(tactic.clone());
    }
    path_tactics.push(tactic);
}

pub(super) fn append_surface_step_to_leaves(
    steps: &mut Vec<SimpleProofStep>,
    step: SimpleProofStep,
) {
    if let Some(SimpleProofStep::If {
        then_proof,
        else_proof,
        ..
    }) = steps.last_mut()
    {
        append_surface_step_to_leaves(&mut then_proof.steps, step.clone());
        append_surface_step_to_leaves(&mut else_proof.steps, step);
    } else {
        steps.push(step);
    }
}

pub(super) fn append_surface_tactics_by_leaf(
    steps: &mut Vec<SimpleProofStep>,
    path_tactics: &[Vec<ProofTactic>],
) -> Result<(), String> {
    let path_steps = path_tactics
        .iter()
        .map(|tactics| {
            ProofCertificate::from_proof_tactics(tactics)
                .map(|proof| proof.steps)
                .map_err(|error| format!("path contained a non-simple tactic: {error:?}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    // Distinct C execution paths do not necessarily correspond to distinct
    // surface proof branches.  When every path produced the same certificate,
    // it is path-independent and belongs on every existing surface leaf.
    if let Some(common) = path_steps.first()
        && path_steps.iter().all(|path| path == common)
    {
        for step in common {
            append_surface_step_to_leaves(steps, step.clone());
        }
        return Ok(());
    }

    pub(super) fn append(
        steps: &mut Vec<SimpleProofStep>,
        path_steps: &[Vec<SimpleProofStep>],
        next_path: &mut usize,
    ) {
        if let Some(SimpleProofStep::If {
            then_proof,
            else_proof,
            ..
        }) = steps.last_mut()
        {
            append(&mut then_proof.steps, path_steps, next_path);
            append(&mut else_proof.steps, path_steps, next_path);
        } else if let Some(suffix) = path_steps.get(*next_path) {
            steps.extend(suffix.iter().cloned());
            *next_path += 1;
        }
    }

    let mut next_path = 0;
    append(steps, &path_steps, &mut next_path);
    if next_path == path_steps.len() {
        Ok(())
    } else {
        Err(format!(
            "surface/certificate path coverage diverged at p{next_path}: surface has {next_path} paths but frame certificate has {}",
            path_steps.len()
        ))
    }
}

/// Appends one context's post-execution surface tactics as a flat top-level
/// suffix. A proof-branch context records its branch decision as a
/// [`SurfacePathChoice`]; the tactics it runs after that decision belong after
/// the choice point — where cross-context synthesis will place the surface
/// `if` — not inside the leaves of an earlier execution branch, which would
/// graft one case's closers onto execution paths the case excluded.
pub(super) fn append_surface_tactics_flat(
    steps: &mut Vec<SimpleProofStep>,
    path_tactics: &[Vec<ProofTactic>],
) -> Result<(), String> {
    let Some(common) = path_tactics.first() else {
        return Ok(());
    };
    if !path_tactics.iter().all(|tactics| tactics == common) {
        return Err(
            "proof-branch context paths need differing surface tactics after the branch choice"
                .to_string(),
        );
    }
    let proof = ProofCertificate::from_proof_tactics(common)
        .map_err(|error| format!("path contained a non-simple tactic: {error:?}"))?;
    steps.extend(proof.steps);
    Ok(())
}

/// Appends a path-independent suffix at every leaf of a surface tactic tree.
/// An empty leaf takes the suffix; a leaf that already carries different
/// tactics is a stitching conflict.
pub(super) fn append_surface_tactics_at_every_leaf(
    tactics: &mut Vec<ProofTactic>,
    suffix: &[ProofTactic],
) -> Result<(), String> {
    if let Some(ProofTactic::If(proof_if)) = tactics.last_mut() {
        append_surface_tactics_at_every_leaf(&mut proof_if.then_tactics, suffix)?;
        append_surface_tactics_at_every_leaf(&mut proof_if.else_tactics, suffix)?;
        return Ok(());
    }
    if tactics.is_empty() {
        tactics.extend(suffix.iter().cloned());
        Ok(())
    } else if tactics == suffix {
        Ok(())
    } else {
        Err(
            "a path-independent tactic expansion conflicts with a leaf's existing expansion"
                .to_string(),
        )
    }
}

pub(super) fn append_surface_tactics_at_branch_path(
    tactics: &mut Vec<ProofTactic>,
    branch_path: &[bool],
    suffix: &[ProofTactic],
) -> Result<(), String> {
    pub(super) fn append(
        tactics: &mut Vec<ProofTactic>,
        branch_path: &[bool],
        next_branch: usize,
        suffix: &[ProofTactic],
    ) -> Result<(), String> {
        if let Some(ProofTactic::If(proof_if)) = tactics.last_mut() {
            let selected_then = *branch_path.get(next_branch).ok_or_else(|| {
                "surface branch skeleton has more branches than its execution path".to_string()
            })?;
            return append(
                if selected_then {
                    &mut proof_if.then_tactics
                } else {
                    &mut proof_if.else_tactics
                },
                branch_path,
                next_branch + 1,
                suffix,
            );
        }
        if next_branch != branch_path.len() {
            return Err(format!(
                "execution path has {} branches but the surface skeleton has {next_branch}",
                branch_path.len()
            ));
        }
        if tactics.is_empty() {
            tactics.extend(suffix.iter().cloned());
        } else if tactics != suffix {
            return Err(
                "two execution paths require different tactic expansions at one surface leaf"
                    .to_string(),
            );
        }
        Ok(())
    }

    append(tactics, branch_path, 0, suffix)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn surface_branch_path_for_outcome(
    tactics: &[ProofTactic],
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    program_point_states: &ProgramPointStates,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<bool>, String> {
    let mut branch_path = Vec::new();
    let mut current = tactics;
    loop {
        let Some(proof_if) = current.iter().rev().find_map(|tactic| match tactic {
            ProofTactic::If(proof_if) => Some(proof_if),
            _ => None,
        }) else {
            return Ok(branch_path);
        };
        let lowered = lower_outcome_proposition_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            available,
            &proof_if.condition,
            predicate_environment,
            click_function_environment,
            program_point_states,
        )?;
        let assumptions = assumptions_from_propositions(available);
        let is_true = exact_fact_is_available(&lowered, available) || assumptions.proves(&lowered);
        let is_false = available
            .iter()
            .any(|fact| propositions_are_exact_negations(fact, &lowered))
            || fact_conflicts_with_assumptions(&lowered, &assumptions);
        let selected_then = match (is_true, is_false) {
            (true, false) => true,
            (false, true) => false,
            (false, false) => {
                return Err(format!(
                    "execution path does not decide surface branch `{}`",
                    describe_click_proposition(&proof_if.condition)
                ));
            }
            (true, true) => {
                return Err(format!(
                    "execution path proves both sides of surface branch `{}`",
                    describe_click_proposition(&proof_if.condition)
                ));
            }
        };
        branch_path.push(selected_then);
        current = if selected_then {
            &proof_if.then_tactics
        } else {
            &proof_if.else_tactics
        };
    }
}

pub(super) fn surface_branch_skeleton(steps: &[SimpleProofStep]) -> Vec<SimpleProofStep> {
    let Some((condition, then_proof, else_proof)) =
        steps.iter().rev().find_map(|step| match step {
            SimpleProofStep::If {
                condition,
                then_proof,
                else_proof,
            } => Some((condition, then_proof, else_proof)),
            _ => None,
        })
    else {
        return Vec::new();
    };
    vec![SimpleProofStep::If {
        condition: condition.clone(),
        then_proof: Box::new(ProofCertificate::from_steps(surface_branch_skeleton(
            then_proof.steps(),
        ))),
        else_proof: Box::new(ProofCertificate::from_steps(surface_branch_skeleton(
            else_proof.steps(),
        ))),
    }]
}

pub(super) fn synthesize_surface_alternatives(
    paths: Vec<ProofCertificateBuilder>,
) -> Result<Vec<SimpleProofStep>, String> {
    if paths.is_empty() {
        return Err("certified alternatives contained no paths".to_string());
    }
    if let Some(blocker) = paths.iter().find_map(|path| path.blocker.clone()) {
        return Err(blocker);
    }
    synthesize_surface_paths(paths)
}

pub(super) fn synthesize_surface_paths(
    paths: Vec<ProofCertificateBuilder>,
) -> Result<Vec<SimpleProofStep>, String> {
    if paths.len() == 1 {
        return Ok(paths.into_iter().next().unwrap().steps);
    }
    let first_choice = paths
        .first()
        .and_then(|path| path.path_choices.first())
        .ok_or_else(|| "distinct certified paths have no surface branch condition".to_string())?
        .clone();
    let prefix = paths[0]
        .steps
        .get(..first_choice.tactic_offset)
        .ok_or_else(|| "surface branch offset exceeds its tactic trace".to_string())?
        .to_vec();

    let mut then_paths = Vec::new();
    let mut else_paths = Vec::new();
    for mut path in paths {
        let choice = path
            .path_choices
            .first()
            .ok_or_else(|| "only some certified paths contain a branch condition".to_string())?
            .clone();
        if choice.occurrence != first_choice.occurrence
            || choice.condition != first_choice.condition
            || choice.tactic_offset != first_choice.tactic_offset
            || path.steps.get(..choice.tactic_offset) != Some(prefix.as_slice())
        {
            return Err("certified paths do not share one branch prefix".to_string());
        }
        path.steps.drain(..choice.tactic_offset);
        path.path_choices.remove(0);
        for remaining in &mut path.path_choices {
            remaining.tactic_offset -= choice.tactic_offset;
        }
        if choice.value {
            then_paths.push(path);
        } else {
            else_paths.push(path);
        }
    }

    if then_paths.is_empty() {
        let mut tactics = prefix;
        tactics.extend(synthesize_surface_paths(else_paths)?);
        return Ok(tactics);
    }
    if else_paths.is_empty() {
        let mut tactics = prefix;
        tactics.extend(synthesize_surface_paths(then_paths)?);
        return Ok(tactics);
    }

    let mut steps = prefix;
    steps.push(SimpleProofStep::If {
        condition: first_choice.condition,
        then_proof: Box::new(ProofCertificate::from_steps(synthesize_surface_paths(
            then_paths,
        )?)),
        else_proof: Box::new(ProofCertificate::from_steps(synthesize_surface_paths(
            else_paths,
        )?)),
    });
    Ok(steps)
}

#[derive(Clone)]
pub(super) enum PostExecutionTactic {
    Fold(ResourceClause),
    CloseOpen {
        resource: ResourceClause,
        preserve_exposed_body: bool,
    },
    UnfoldPredicate(String),
    Apply(TheoremApplication),
    ApplyUsing {
        application: TheoremApplication,
        premises: Vec<ClickProposition>,
    },
    Have(ProofHave),
    Transport {
        source: ClickProposition,
        target: ClickProposition,
        premises: Option<Vec<ClickProposition>>,
    },
    Choose(ProofChoice),
    Witness(ProofWitness),
    Assumption,
    Normalize,
    Rewrite(ClickProposition),
    FrameRegion(CodeRegionRef),
    Frame,
    FrameUsing {
        region: Option<CodeRegionRef>,
        premises: Vec<ClickProposition>,
    },
    CheckedFrameUsing {
        authority: CheckedFrameAuthority,
        region: Option<CodeRegionRef>,
        premises: Vec<ClickProposition>,
        /// Exact checked Surface contribution retained until ordered
        /// finalization reaches this source operation. This is expansion
        /// provenance only; the other fields are the complete semantic input.
        surface_tactics: Option<Vec<ProofTactic>>,
    },
    /// Surface-only control structure scheduled after terminal execution.
    /// The arms contain no semantic state: ordered finalization asks the
    /// focused outcome `Proof` to decide the condition, then applies only the
    /// selected arm's ordinary checked operations to that same descendant.
    If {
        condition: ClickProposition,
        then_tactics: Vec<DeferredPostExecutionTactic>,
        else_tactics: Vec<DeferredPostExecutionTactic>,
    },
    Simp,
}

#[derive(Clone)]
pub(super) struct DeferredPostExecutionTactic {
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) tactic: PostExecutionTactic,
    /// The tactic's surface steps are already retained by checked `Proof`
    /// provenance or a legacy surface record. The exit drain performs only
    /// the deferred outcome work and must not record those steps again.
    pub(super) surface_recorded: bool,
}

#[cfg(test)]
mod proof_fact_store_tests {
    use super::*;

    fn fact(value: bool) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::Constant(value), true)
    }

    #[test]
    fn proof_fact_store_preserves_order_and_indexes_exact_membership() {
        let first = fact(true);
        let second = fact(false);
        let mut facts = ProofFactStore::default();

        assert!(facts.insert(first.clone()));
        assert!(facts.insert(second.clone()));
        assert!(!facts.insert(first.clone()));
        assert_eq!(facts.to_vec(), &[first.clone(), second.clone()]);
        assert!(facts.exact.contains(&first));

        facts.retain(|candidate| candidate != &first);
        assert_eq!(facts.to_vec(), std::slice::from_ref(&second));
        assert!(!facts.exact.contains(&first));
        assert!(facts.exact.contains(&second));
    }

    #[test]
    fn proof_fact_store_forks_share_certificate_history() {
        let mut facts = ProofFactStore::default();
        for index in 0..4096 {
            facts.insert(Proposition::ConditionIs(
                ConditionTerm::Variable(Variable(index)),
                true,
            ));
        }
        let ancestor = facts.clone();
        assert!(facts.shares_persistent_storage_with(&ancestor));

        let added = Proposition::ConditionIs(ConditionTerm::Variable(Variable(4096)), true);
        facts.insert(added.clone());

        assert!(!ancestor.contains(&added));
        assert!(facts.contains(&added));
        assert_eq!(ancestor.iter().count(), 4096);
        assert_eq!(facts.iter().count(), 4097);
    }

    #[test]
    fn persistent_sequence_forks_share_history_and_preserve_order() {
        let mut sequence = PersistentSequence::default();
        for value in 0..4096 {
            sequence.push(value);
        }
        let ancestor = sequence.clone();
        assert!(sequence.shares_tail_with(&ancestor));

        sequence.push(4096);

        assert_eq!(
            ancestor.iter().copied().collect::<Vec<_>>(),
            (0..4096).collect::<Vec<_>>()
        );
        assert_eq!(
            sequence.iter().copied().collect::<Vec<_>>(),
            (0..=4096).collect::<Vec<_>>()
        );
        assert!(!sequence.shares_tail_with(&ancestor));
        assert_eq!(ancestor.tail.as_ref().map(Arc::strong_count), Some(2));
    }

    #[test]
    fn persistent_sequence_drops_large_shared_histories_iteratively() {
        let mut sequence = PersistentSequence::default();
        for value in 0..16_384 {
            sequence.push(value);
        }
        let ancestor = sequence.clone();
        sequence.push(16_384);

        drop(sequence);
        assert_eq!(ancestor.len(), 16_384);
        drop(ancestor);
    }

    #[test]
    fn execution_frontier_forks_share_remaining_c_and_continuation_history() {
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut statement = CStatement::Skip;
            for _ in 0..size {
                statement = c_seq(CStatement::Skip, statement);
            }
            let remaining = Arc::new(statement);
            let mut frontier = ExecutionFrontier {
                point: ProofExecutionPoint::StatementEntry {
                    remaining: remaining.clone(),
                },
                continuations: PersistentSequence::default(),
                ..ExecutionFrontier::default()
            };
            frontier.continuations.push(ProofExecutionContinuation {
                remaining: Some(remaining.clone()),
                next_statement_index: 1,
                kind: ProofExecutionContinuationKind::LoopIteration,
            });
            let ancestor = frontier.clone();

            let (
                ProofExecutionPoint::StatementEntry {
                    remaining: fork_remaining,
                },
                ProofExecutionPoint::StatementEntry {
                    remaining: ancestor_remaining,
                },
            ) = (&frontier.point, &ancestor.point)
            else {
                panic!("test frontiers should remain at statement entry")
            };
            assert!(Arc::ptr_eq(fork_remaining, ancestor_remaining));
            assert!(
                frontier
                    .continuations
                    .shares_tail_with(&ancestor.continuations),
                "size {size} frontier clone copied its continuation history"
            );

            frontier.continuations.push(ProofExecutionContinuation {
                remaining: Some(remaining.clone()),
                next_statement_index: 2,
                kind: ProofExecutionContinuationKind::LoopIteration,
            });
            let local_tail = frontier
                .continuations
                .tail
                .as_ref()
                .expect("local continuation");
            assert!(Arc::ptr_eq(
                local_tail.parent.as_ref().expect("shared parent"),
                ancestor.continuations.tail.as_ref().expect("ancestor tail")
            ));
            assert_eq!(ancestor.continuations.len(), 1);
            assert_eq!(frontier.continuations.len(), 2);
            assert_eq!(
                frontier
                    .continuations
                    .pop()
                    .expect("local continuation")
                    .next_statement_index,
                2
            );
            assert!(
                frontier
                    .continuations
                    .shares_tail_with(&ancestor.continuations),
                "popping the local suffix should restore the shared ancestor stack"
            );
        }
    }

    #[test]
    fn persistent_ordered_set_forks_and_local_insertions_scale_logarithmically() {
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut set = PersistentOrderedSet::default();
            for value in 0..size {
                assert!(set.insert(value));
            }
            let ancestor = set.clone();
            assert!(set.exact.shares_root_with(&ancestor.exact));
            assert!(set.ordered.shares_tail_with(&ancestor.ordered));

            let before = persistent_node_allocations();
            assert!(set.insert(size));
            let allocations = persistent_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 4 * logarithmic_height + 8;
            assert!(
                allocations <= allocation_bound,
                "size {size} local insertion allocated {allocations} set nodes (bound {allocation_bound})"
            );
            assert!(!ancestor.contains(&size));
            assert!(set.contains(&size));
            assert_eq!(
                set.iter().copied().collect::<Vec<_>>(),
                (0..=size).collect::<Vec<_>>()
            );

            let before_duplicate = persistent_node_allocations();
            assert!(!set.insert(size));
            assert_eq!(persistent_node_allocations(), before_duplicate);
        }
    }

    #[test]
    fn ordered_set_introduced_since_reports_only_new_members() {
        let mut set = PersistentOrderedSet::default();
        set.insert(1u32);
        set.insert(2);
        let ancestor = set.clone();
        set.insert(3);
        set.insert(2);
        set.insert(4);

        assert_eq!(set.introduced_since(&ancestor), Some(vec![3, 4]));
        assert_eq!(ancestor.introduced_since(&ancestor), Some(Vec::new()));
        assert_eq!(ancestor.introduced_since(&set), None);
    }

    #[test]
    fn shared_vec_suffix_since_reports_the_appended_entries() {
        let mut history = SharedVec::from(vec![1u32, 2]);
        let ancestor = history.clone();
        history.push(3);
        history.push(4);

        assert_eq!(history.suffix_since(&ancestor), Some(&[3u32, 4][..]));
        assert_eq!(ancestor.suffix_since(&ancestor), Some(&[][..]));
        assert_eq!(ancestor.suffix_since(&history), None);
    }
}

pub(super) fn post_execution_tactic_timing(
    post_tactic: &PostExecutionTactic,
) -> (&'static str, &'static str) {
    match post_tactic {
        PostExecutionTactic::Apply(_) => ("apply", "smart"),
        PostExecutionTactic::Have(have) => (
            "have",
            if smart_simp_unfold_prefix(&have.proof).is_some() {
                "smart"
            } else {
                "control"
            },
        ),
        PostExecutionTactic::Transport { premises, .. } => (
            "transport",
            if premises.is_some() {
                "simple"
            } else {
                "smart"
            },
        ),
        PostExecutionTactic::Simp => ("simp", "smart"),
        PostExecutionTactic::Fold(_) => ("fold", "simple"),
        PostExecutionTactic::CloseOpen { .. } => ("open", "control"),
        PostExecutionTactic::UnfoldPredicate(_) => ("unfold", "simple"),
        PostExecutionTactic::ApplyUsing { .. } => ("apply", "simple"),
        PostExecutionTactic::Choose(_) => ("choose", "simple"),
        PostExecutionTactic::Witness(_) => ("witness", "simple"),
        PostExecutionTactic::Assumption => ("assumption", "simple"),
        PostExecutionTactic::Normalize => ("normalize", "simple"),
        PostExecutionTactic::Rewrite(_) => ("rewrite", "simple"),
        PostExecutionTactic::FrameRegion(_) => ("frame", "simple"),
        PostExecutionTactic::Frame => ("frame", "simple"),
        PostExecutionTactic::FrameUsing { .. } | PostExecutionTactic::CheckedFrameUsing { .. } => {
            ("frame", "simple")
        }
        PostExecutionTactic::If { .. } => ("if", "control"),
    }
}

/// The typed identity of the execution region a frontier executes. A
/// whole-function frontier must end at a `return`; a loop-preservation
/// frontier owns exactly the loop body's statement tree, so exhausting that
/// tree reaches the typed back-edge boundary instead of erring. The region
/// kind is declared at frontier construction and never changes.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(super) enum ExecutionRegionKind {
    #[default]
    Function,
    LoopBody,
    /// One arm of a C `if`: the arm frontier owns exactly the arm's own
    /// statement tree, so its join composes on the typed boundary without a
    /// completed-region set or continuation-depth bookkeeping.
    BranchArm,
}

#[derive(Clone, Default)]
pub(super) struct ExecutionFrontier {
    pub(super) point: ProofExecutionPoint,
    pub(super) region: ExecutionRegionKind,
    pub(super) execution_start_state: Option<CState>,
    pub(super) next_statement_index: usize,
    pub(super) continuations: PersistentSequence<ProofExecutionContinuation>,
}

#[derive(Clone)]
pub(super) struct ProofExecutionContinuation {
    pub(super) remaining: Option<Arc<CStatement>>,
    pub(super) next_statement_index: usize,
    pub(super) kind: ProofExecutionContinuationKind,
}

#[derive(Clone, Copy)]
pub(super) enum ProofExecutionContinuationKind {
    LoopIteration,
}

#[derive(Clone, Default)]
pub(super) enum ProofExecutionPoint {
    #[default]
    FunctionEntry,
    StatementEntry {
        remaining: Arc<CStatement>,
    },
    FunctionExit {
        execution: CFunctionExecutionCandidates,
    },
    /// Execution exhausted a bounded region's own statement tree with no
    /// enclosing continuation: the typed loop back-edge boundary. The
    /// frontier owns no code at this point, so executing past the boundary
    /// is unrepresentable rather than detected after the fact.
    RegionBoundary,
}
impl ExecutionFrontier {
    pub(super) fn is_at_function_exit(&self) -> bool {
        matches!(self.point, ProofExecutionPoint::FunctionExit { .. })
    }

    pub(super) fn is_at_function_entry(&self) -> bool {
        matches!(self.point, ProofExecutionPoint::FunctionEntry)
    }

    /// Execution reached the typed back-edge boundary of a bounded region:
    /// the region's own statement tree is exhausted and no enclosing
    /// continuation remains.
    pub(super) fn is_at_region_boundary(&self) -> bool {
        matches!(self.point, ProofExecutionPoint::RegionBoundary)
    }

    pub(super) fn execution(&self) -> Option<&CFunctionExecutionCandidates> {
        match &self.point {
            ProofExecutionPoint::FunctionEntry
            | ProofExecutionPoint::StatementEntry { .. }
            | ProofExecutionPoint::RegionBoundary => None,
            ProofExecutionPoint::FunctionExit { execution, .. } => Some(execution),
        }
    }

    pub(super) fn execution_start_state<'a>(&'a self, current_state: &'a CState) -> &'a CState {
        self.execution_start_state.as_ref().unwrap_or(current_state)
    }
}

/// The state that `old(...)` and `at(function.entry, ...)` resolve to when
/// a contract clause is lowered here.
///
/// This is the one place that answers "which memory does `old` mean", so
/// the answer is a *named* snapshot rather than whichever state happens to
/// sit at the enclosing frame's `pre_state` position. When the region
/// recorded its function-entry snapshot, that snapshot is the answer —
/// it is the same `CState` the Click -> Spec lowering used as
/// `SpecMemory::Fixed(entry_memory)` for every `old` operand in this
/// function's contracts, so both sides name the same interned node.
///
/// Nothing here is trusted on the strength of the naming alone. A lowered
/// candidate is accepted only by exact equality against the certified
/// proposition, and a `MemoryLoad` carries its snapshot inside the term,
/// so a candidate resolved to the wrong state cannot match: selecting the
/// state by name adds a form to search, and the certificate check
/// remains the thing that validates it.
///
/// Falling back to [`ExecutionFrontier::execution_start_state`] keeps every region that
/// records no function-entry snapshot on its previous behaviour.
pub(super) fn old_reference_state<'a>(
    function_entry_state: Option<&'a CState>,
    frontier: &'a ExecutionFrontier,
    current_state: &'a CState,
) -> &'a CState {
    match function_entry_state {
        Some(entry_state) => entry_state,
        None => frontier.execution_start_state(current_state),
    }
}

/// The execution data that lowering and point proofs read: the frontier,
/// the recorded program-point states, the surface spellings, the effect
/// facts, and the state `old(...)` resolves to. Owners build it from
/// wherever they keep those fields, so consumers do not depend on the
/// replay bag's layout.
#[derive(Clone, Copy)]
pub(super) struct ExecutionView<'a> {
    pub(super) frontier: &'a ExecutionFrontier,
    pub(super) program_point_states: &'a ProgramPointStates,
    pub(super) surface_propositions: &'a SurfacePropositionMap,
    pub(super) effect_facts: &'a [ExecutionPureFact],
    function_entry_state: Option<&'a CState>,
}

impl<'a> ExecutionView<'a> {
    /// The state the current region started from, or the current state
    /// when no region is open.
    pub(super) fn execution_start_state<'s>(&self, current_state: &'s CState) -> &'s CState
    where
        'a: 's,
    {
        self.frontier
            .execution_start_state
            .as_ref()
            .unwrap_or(current_state)
    }

    /// The state that `old(...)` and `at(function.entry, ...)` resolve to when
    /// a contract clause is lowered here.
    pub(super) fn old_reference_state<'s>(&self, current_state: &'s CState) -> &'s CState
    where
        'a: 's,
    {
        match self.function_entry_state {
            Some(entry_state) => entry_state,
            None => self.execution_start_state(current_state),
        }
    }
}

impl<'a> ExecutionView<'a> {
    pub(super) fn new(
        frontier: &'a ExecutionFrontier,
        effect_facts: &'a [ExecutionPureFact],
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        function_entry_state: Option<&'a CState>,
    ) -> Self {
        ExecutionView {
            frontier,
            program_point_states,
            surface_propositions,
            effect_facts,
            function_entry_state,
        }
    }
}
