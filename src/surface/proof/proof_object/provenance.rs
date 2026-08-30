//! Checked derivation lineage and certificate extraction.

use super::*;

/// An opaque position in one `Proof` derivation.
///
/// This retains no semantic state. Structured joins use it to extract only the
/// already-checked descendant steps for an arm.
#[derive(Clone)]
pub(in crate::surface::proof) struct ProofCheckpoint<'a> {
    pub(super) context: Arc<ProofContext<'a>>,
    pub(super) node: Arc<ProofNode>,
}

#[derive(Clone, Copy)]
pub(super) struct ProofStepOrigin {
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
}

/// Private persistent surface-provenance node.
///
/// This lineage serializes already-checked operations; it does not own the
/// semantic state or grant authority to construct a successor.
pub(super) struct ProofNode {
    pub(super) parent: Option<Arc<ProofNode>>,
    pub(super) step: Option<Arc<ProofStep>>,
    /// The goal the step advanced (or, for markers, introduced). Certificate
    /// extraction partitions an interleaved multi-goal derivation by this
    /// recorded attribution; it never infers ownership from final states.
    pub(super) focused_branch: BranchId,
    pub(super) depth: usize,
}

impl<'a> Proof<'a> {
    /// The certificate of the focused branch goal's own lineage. Steps in the
    /// derivation are attributed to the goal they advanced; on an unjoined
    /// case-split arm, sibling arms' steps interleave in the same chain and
    /// belong to other lineages. A step-less marker node records the goal
    /// that was live before it (the split's parent), so walking back
    /// through markers follows the lineage to the root.
    pub(in crate::surface::proof) fn path_certificate(&self) -> ProofCertificate {
        let mut steps = Vec::new();
        let mut goal = self.focused_branch_id();
        let mut node = Some(self.node.clone());
        while let Some(current) = node {
            match &current.step {
                Some(step) if current.focused_branch == goal => steps.push(step.as_ref().clone()),
                Some(_) => {}
                None => goal = current.focused_branch,
            }
            node = current.parent.clone();
        }
        steps.reverse();
        ProofCertificate::from_steps(steps)
    }

    pub(super) fn certificate_after_node(
        &self,
        ancestor: Option<&Arc<ProofNode>>,
    ) -> Result<ProofCertificate, ClickError> {
        let expected_depth = ancestor.map_or(0, |node| node.depth);
        let mut steps = Vec::with_capacity(self.node.depth.saturating_sub(expected_depth));
        let mut node = Some(self.node.clone());
        while let Some(current) = node {
            if ancestor.is_some_and(|ancestor| Arc::ptr_eq(ancestor, &current)) {
                steps.reverse();
                return Ok(ProofCertificate::from_steps(steps));
            }
            if let Some(step) = &current.step {
                steps.push(step.as_ref().clone());
            }
            node = current.parent.clone();
        }
        if ancestor.is_some() {
            return Err(
                self.step_error("certificate validationpoint is not an ancestor of this proof")
            );
        }
        steps.reverse();
        Ok(ProofCertificate::from_steps(steps))
    }
}
