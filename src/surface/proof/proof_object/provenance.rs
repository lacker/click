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

/// Which block of the written proof a step position counts within.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(super) enum ProofStepBlock {
    /// The claim's own `by { ... }` script.
    #[default]
    Claim,
    /// The `by { ... }` block of a `have`.
    Have,
    /// The body of an `open`.
    Open,
}

impl ProofStepBlock {
    fn name(self) -> &'static str {
        match self {
            Self::Claim => "proof",
            Self::Have => "have body",
            Self::Open => "open body",
        }
    }
}

/// How one block addresses the step being checked.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ProofStepPosition {
    /// The claim's source tactic occurrence, numbered exactly as `click
    /// expand` and `click profile` address it.
    SourceTactic(usize),
    /// The zero-based position of the tactic within the block the user wrote.
    InBlock(usize),
}

impl ProofStepPosition {
    fn describe(self, block: ProofStepBlock) -> String {
        match self {
            Self::SourceTactic(index) => format!("source tactic {index}"),
            Self::InBlock(index) => format!("{} tactic {}", block.name(), index + 1),
        }
    }
}

/// Where the step being checked sits in the proof the user wrote: the chain
/// of enclosing `have`/`open` blocks, innermost last, with each block's
/// current source position.
///
/// This is diagnostic addressing only. It carries no semantic state and
/// grants no authority; a step checks exactly the same way whether or not its
/// driver has attributed a source position.
#[derive(Clone, Default)]
pub(in crate::surface::proof) struct ProofStepSite {
    enclosing: Option<Arc<ProofStepSite>>,
    block: ProofStepBlock,
    position: Option<ProofStepPosition>,
}

impl ProofStepSite {
    /// The same site addressing the claim's `index`th source tactic
    /// occurrence.
    pub(super) fn at_source_tactic(&self, index: usize) -> Self {
        self.with_position(ProofStepPosition::SourceTactic(index))
    }

    /// The same site addressing the `index`th tactic written in the innermost
    /// block.
    pub(super) fn at_block_position(&self, index: usize) -> Self {
        self.with_position(ProofStepPosition::InBlock(index))
    }

    fn with_position(&self, position: ProofStepPosition) -> Self {
        Self {
            enclosing: self.enclosing.clone(),
            block: self.block,
            position: Some(position),
        }
    }

    /// The site of a step inside a nested `have` or `open` block opened at
    /// this site.
    pub(super) fn nested(&self, block: ProofStepBlock) -> Self {
        Self {
            enclosing: Some(Arc::new(self.clone())),
            block,
            position: None,
        }
    }

    /// Whether the innermost block already addresses source tactic `index`.
    pub(super) fn addresses_source_tactic(&self, index: usize) -> bool {
        self.position == Some(ProofStepPosition::SourceTactic(index))
    }

    /// Whether the innermost block already addresses its `index`th written
    /// tactic.
    pub(super) fn addresses_block_position(&self, index: usize) -> bool {
        self.position == Some(ProofStepPosition::InBlock(index))
    }

    fn segments(&self, into: &mut Vec<String>) {
        if let Some(enclosing) = &self.enclosing {
            enclosing.segments(into);
        }
        if let Some(position) = self.position {
            into.push(position.describe(self.block));
        }
    }

    /// The source path of the step being checked, outermost block first, or
    /// `None` when no driver attributed a source position to it.
    pub(super) fn path(&self) -> Option<String> {
        let mut segments = Vec::new();
        self.segments(&mut segments);
        (!segments.is_empty()).then(|| segments.join(" > "))
    }
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
