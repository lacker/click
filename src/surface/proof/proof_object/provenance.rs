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
    /// One arm of a structured proof tactic (`if`, `cases`, or `both`)
    /// written in a block. `index` is the arm's written position (0 for the
    /// first arm) and `name` is how the source spells it.
    Arm { index: usize, name: &'static str },
}

impl ProofStepBlock {
    fn name(self) -> String {
        match self {
            Self::Claim => "proof".to_string(),
            Self::Have => "have body".to_string(),
            Self::Open => "open body".to_string(),
            Self::Arm { name, .. } => format!("{name} arm"),
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
            Self::SourceTactic(index) => format!("tactic {index}"),
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
    /// Planner-generated block positions can attribute checked steps for
    /// tracing, but never identify a written occurrence for expansion.
    generated: bool,
}

impl ProofStepSite {
    /// The same site addressing the claim's `index`th source tactic
    /// occurrence.
    ///
    /// A generated tactic carries `usize::MAX` in place of a source index:
    /// nobody wrote it, so the site addresses no written tactic.
    pub(in crate::surface::proof) fn at_source_tactic(&self, index: usize) -> Self {
        if index == usize::MAX {
            return Self {
                enclosing: self.enclosing.clone(),
                block: self.block,
                position: None,
                generated: true,
            };
        }
        let mut site = self.with_position(ProofStepPosition::SourceTactic(index));
        site.generated = false;
        site
    }

    /// The same site addressing the `index`th tactic written in the innermost
    /// block.
    pub(in crate::surface::proof) fn at_block_position(&self, index: usize) -> Self {
        self.with_position(ProofStepPosition::InBlock(index))
    }

    /// The site of the `index`th tactic written in the body of the `have`
    /// this site addresses.
    pub(in crate::surface::proof) fn in_have_body(&self, index: usize) -> Self {
        self.nested(ProofStepBlock::Have).at_block_position(index)
    }

    /// The site of the `index`th tactic written in arm `arm` (spelled
    /// `name`) of the structured tactic this site addresses.
    pub(in crate::surface::proof) fn in_arm(
        &self,
        arm: usize,
        name: &'static str,
        index: usize,
    ) -> Self {
        self.nested(ProofStepBlock::Arm { index: arm, name })
            .at_block_position(index)
    }

    fn with_position(&self, position: ProofStepPosition) -> Self {
        Self {
            enclosing: self.enclosing.clone(),
            block: self.block,
            position: Some(position),
            generated: self.generated,
        }
    }

    /// The site of a step inside a nested `have` or `open` block, or an arm
    /// of a structured tactic, opened at this site.
    pub(super) fn nested(&self, block: ProofStepBlock) -> Self {
        Self {
            enclosing: Some(Arc::new(self.clone())),
            block,
            position: None,
            generated: self.generated,
        }
    }

    /// Whether the innermost block already addresses source tactic `index`.
    pub(super) fn addresses_source_tactic(&self, index: usize) -> bool {
        self.position == Some(ProofStepPosition::SourceTactic(index))
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

    /// The source path of the step being checked: the claim-level source
    /// index of its outermost tactic, then, for each block it descends into,
    /// the written position there. A `have` or `open` body contributes one
    /// entry (the position in the body); an arm of a structured tactic
    /// contributes two (the arm's written position, then the position in the
    /// arm). Every written tactic therefore has its own path, and the source
    /// mapper decodes it by reading which tactic each prefix names.
    /// The source path used to select a written occurrence for expansion.
    /// Generated checking steps retain trace attribution to their enclosing
    /// source body, but must not claim an independent written occurrence.
    pub(in crate::surface::proof) fn written_source_tactic_path(&self) -> Option<Vec<usize>> {
        if self.generated {
            None
        } else {
            self.source_tactic_path()
        }
    }

    pub(super) fn source_tactic_path(&self) -> Option<Vec<usize>> {
        let mut path = if let Some(enclosing) = &self.enclosing {
            enclosing.source_tactic_path()?
        } else {
            Vec::new()
        };
        let Some(position) = self.position else {
            return (!path.is_empty()).then_some(path);
        };
        match position {
            ProofStepPosition::SourceTactic(index) if path.is_empty() => path.push(index),
            ProofStepPosition::InBlock(index) if !path.is_empty() => {
                if let ProofStepBlock::Arm { index: arm, .. } = self.block {
                    path.push(arm);
                }
                path.push(index);
            }
            _ => return None,
        }
        Some(path)
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
    /// For a split marker, the goals the split opened. Sibling arms of one
    /// split share this chain, so a marker is on a walking lineage only when
    /// it opened the goal that lineage is currently following. An empty list
    /// is a marker that opened no goal of its own; the walk then treats it as
    /// the enclosing structural marker it is.
    pub(super) split_branches: Vec<BranchId>,
    /// The lineage certificate this node ends, per goal that a walk reached
    /// it following: see [`Proof::path_certificate`]. Filled the first time a
    /// walk passes, so a later walk stops at the first node one already
    /// answered for instead of re-reading the whole history behind it.
    pub(super) path_memo: std::sync::Mutex<Vec<(BranchId, Arc<PathSteps>)>>,
}

/// One goal's lineage steps up to some node, newest first, shared between the
/// nodes whose lineages coincide below it. `invalid` and `arithmetic_using`
/// summarize the two checks [`ProofCertificate::from_steps`] applies to the
/// list, each computed once for the step this link adds: a list passes those
/// checks exactly when every step does.
pub(super) struct PathSteps {
    link: Option<(Arc<ProofStep>, Arc<PathSteps>)>,
    len: usize,
    invalid: bool,
    arithmetic_using: bool,
}

impl PathSteps {
    fn empty() -> Arc<Self> {
        Arc::new(Self {
            link: None,
            len: 0,
            invalid: false,
            arithmetic_using: false,
        })
    }

    fn extended(step: &Arc<ProofStep>, earlier: &Arc<Self>) -> Arc<Self> {
        crate::instrumentation::record_deterministic_work(1);
        let invalid = earlier.invalid
            || crate::surface::validate_certificate_step(step, earlier.len, &mut Vec::new())
                .is_err();
        Arc::new(Self {
            link: Some((step.clone(), earlier.clone())),
            len: earlier.len + 1,
            invalid,
            arithmetic_using: earlier.arithmetic_using
                || crate::surface::proof_step_contains_arithmetic_using(step),
        })
    }

    /// The steps in proof order.
    fn to_vec(&self) -> Vec<ProofStep> {
        let mut steps = Vec::with_capacity(self.len);
        let mut link = &self.link;
        while let Some((step, earlier)) = link {
            crate::instrumentation::record_deterministic_work(1);
            steps.push(step.as_ref().clone());
            link = &earlier.link;
        }
        steps.reverse();
        steps
    }
}

impl ProofNode {
    /// A split or scope marker under `parent`: no step, the parent's depth,
    /// opening `split_branches` for `focused_branch`.
    pub(super) fn marker(
        parent: &Arc<ProofNode>,
        focused_branch: BranchId,
        split_branches: Vec<BranchId>,
    ) -> Arc<Self> {
        Arc::new(Self {
            path_memo: Default::default(),
            parent: Some(parent.clone()),
            step: None,
            focused_branch,
            depth: parent.depth,
            split_branches,
        })
    }

    /// One recorded step under `parent`, advancing `focused_branch`.
    pub(super) fn step_child(
        parent: &Arc<ProofNode>,
        focused_branch: BranchId,
        step: Arc<ProofStep>,
    ) -> Arc<Self> {
        Arc::new(Self {
            path_memo: Default::default(),
            parent: Some(parent.clone()),
            step: Some(step),
            focused_branch,
            depth: parent.depth + 1,
            split_branches: Vec::new(),
        })
    }

    fn memoized_path(&self, goal: BranchId) -> Option<Arc<PathSteps>> {
        self.path_memo
            .lock()
            .expect("proof path memo")
            .iter()
            .find(|(memo_goal, _)| *memo_goal == goal)
            .map(|(_, steps)| steps.clone())
    }

    /// The steps of `goal`'s lineage that end at this node: the walk
    /// [`Proof::path_certificate`] describes, stopped at the first node an
    /// earlier walk already answered for that goal, with every node it passed
    /// remembered on the way back.
    fn lineage_steps(self: &Arc<Self>, goal: BranchId) -> Arc<PathSteps> {
        let mut walked: Vec<(Arc<ProofNode>, BranchId)> = Vec::new();
        let mut goal = goal;
        let mut node = Some(self.clone());
        let mut base = PathSteps::empty();
        while let Some(current) = node {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(steps) = current.memoized_path(goal) {
                base = steps;
                break;
            }
            let entry_goal = goal;
            if current.step.is_none()
                && (current.split_branches.is_empty() || current.split_branches.contains(&goal))
            {
                goal = current.focused_branch;
            }
            node = current.parent.clone();
            walked.push((current, entry_goal));
        }
        for (current, entry_goal) in walked.into_iter().rev() {
            if let Some(step) = &current.step
                && current.focused_branch == entry_goal
            {
                base = PathSteps::extended(step, &base);
            }
            current
                .path_memo
                .lock()
                .expect("proof path memo")
                .push((entry_goal, base.clone()));
        }
        base
    }
}

impl<'a> Proof<'a> {
    /// The certificate of the focused branch goal's own lineage. Steps in the
    /// derivation are attributed to the goal they advanced; on an unjoined
    /// case-split arm, sibling arms' steps interleave in the same chain and
    /// belong to other lineages. A step-less marker node records the goal
    /// that was live before it (the split's parent), so walking back
    /// through markers follows the lineage to the root. A split marker also
    /// records the goals it opened, and is followed only when it opened the
    /// goal being walked: a split nested inside a sibling arm leaves a marker
    /// naming that sibling, and following it would adopt the sibling arm's
    /// steps as this path's own.
    ///
    /// Each node remembers, per goal, the lineage that ends at it, so this
    /// reads only the nodes added since the last walk that passed this way
    /// and does not re-read sibling arms' history. The steps are checked as
    /// [`ProofCertificate::from_steps`] checks them, one step at a time as
    /// each joins a lineage; a lineage that fails either check is handed to
    /// `from_steps` itself, so the refusal is the one it always was.
    pub(in crate::surface::proof) fn path_certificate(
        &self,
    ) -> Result<ProofCertificate, ClickError> {
        let steps = self.node.lineage_steps(self.focused_branch_id());
        if steps.invalid || steps.arithmetic_using {
            return ProofCertificate::from_steps(steps.to_vec());
        }
        Ok(ProofCertificate::from_admitted_steps(steps.to_vec()))
    }

    /// The number of steps in [`Self::path_certificate`], or its refusal,
    /// without building it.
    pub(in crate::surface::proof) fn path_step_count(&self) -> Result<usize, ClickError> {
        let steps = self.node.lineage_steps(self.focused_branch_id());
        if steps.invalid || steps.arithmetic_using {
            return ProofCertificate::from_steps(steps.to_vec())
                .map(|certificate| certificate.steps().len());
        }
        Ok(steps.len)
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
                return ProofCertificate::from_steps(steps);
            }
            if let Some(step) = &current.step {
                steps.push(step.as_ref().clone());
            }
            node = current.parent.clone();
        }
        if ancestor.is_some() {
            return Err(self.step_error("certificate checkpoint is not an ancestor of this proof"));
        }
        steps.reverse();
        ProofCertificate::from_steps(steps)
    }
}
