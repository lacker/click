//! Opt-in, bounded observations of checked proof steps for CLI diagnostics.
//! The trace is diagnostic only; no recorded text participates in checking.

use crate::kernel::ContractPathPreparationFailure;
use crate::kernel::proof::BranchId;
use crate::kernel::{
    Bitvector32Term, CResourceFact, ConditionTerm, Pointer, Proposition, SharedCMemory,
};
use crate::surface::proof_diagnostics::ProofDiagnosticState;
use crate::surface::proof_diagnostics::render::{self, SnapshotLabels};
use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;

pub(super) const MAX_STEPS: usize = 2048;
const MAX_RENDER_BYTES: usize = 64 * 1024;

struct Capture {
    function: String,
    steps: HashMap<usize, TraceStep>,
    branches: HashMap<usize, TraceBranch>,
    joins: HashMap<usize, TraceJoin>,
    bodies: HashMap<usize, TraceBody>,
    scope_parents: HashMap<usize, TraceScope>,
    limit_reached: bool,
}

#[derive(Clone, Copy)]
pub(super) struct TracePathNode {
    pub node: usize,
    pub selected_arm: Option<BranchId>,
}

pub(super) struct TraceJoin {
    pub marker: usize,
    pub arms: [Vec<TracePathNode>; 2],
    /// Keeps arm provenance alive so later proof attempts cannot recycle its
    /// pointer identities.
    pub _retained: Box<dyn Any>,
}

struct TraceScope {
    lineage: Vec<TracePathNode>,
    _retained: Box<dyn Any>,
}

pub(super) struct TraceBody {
    pub lineage: Vec<TracePathNode>,
    pub _retained: Box<dyn Any>,
}

pub(super) struct TraceBranch {
    pub header: String,
    pub arms: [(BranchId, Vec<TraceFact>); 2],
}

pub(super) struct TraceStep {
    pub header: String,
    pub call_source: Option<TraceCallSource>,
    pub facts: Vec<TraceFact>,
    pub more_facts: usize,
    pub frontier: Option<String>,
    pub resources: Vec<(usize, usize, CResourceFact)>,
    pub more_resources: usize,
}

/// Written call context, deliberately separate from exact checked facts.
/// Instantiating a callee guarantee with an evaluated historical load can
/// produce a fact that no Click proposition currently lowers to exactly.
pub(super) struct TraceCallSource {
    pub call: String,
    pub guarantees: Vec<String>,
    pub more_guarantees: usize,
}

pub(super) struct TraceFact {
    pub kernel: Proposition,
    /// A form re-lowered to this exact fact at the checked step. A generated
    /// fact without such a form remains explicitly internal in the report.
    pub source: Option<String>,
}

/// The exact check that failed after the written proof completed. A completed
/// script has no failing proof node, so it cannot use a node-lineage trace.
/// These facts come from the certification context at the failed check.
pub(super) struct CertificationTraceState {
    goal: Proposition,
    source_goal: Option<String>,
    available: Vec<Proposition>,
    available_count: usize,
}

impl CertificationTraceState {
    pub(super) fn from_failure(failure: &ContractPathPreparationFailure) -> Option<Self> {
        Some(Self {
            goal: failure.obligation.clone()?,
            source_goal: failure.source_goal.clone(),
            available: failure.available.clone(),
            available_count: failure.available_count,
        })
    }
}

fn traced_read(term: &Bitvector32Term) -> Option<(SharedCMemory, Pointer)> {
    match term {
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            Some((memory.clone(), pointer.as_ref().clone()))
        }
        Bitvector32Term::Variable(variable) => {
            crate::kernel::registered_load_for_variable(variable)
        }
        _ => None,
    }
}

impl ProofDiagnosticState for CertificationTraceState {
    fn source_goal(&self) -> Option<String> {
        self.source_goal.clone()
    }

    fn kernel_goal(&self) -> Option<&Proposition> {
        Some(&self.goal)
    }

    fn premises(&self, _limit: usize) -> Vec<&Proposition> {
        Vec::new()
    }

    fn premise_count(&self) -> usize {
        0
    }

    fn proof_trace(&self, _claim: &str, labels: &mut SnapshotLabels) -> Option<String> {
        let mut output =
            String::from("  certification trace (facts available at the failed check):");
        let mut relevant = Vec::new();
        let mut different_snapshots = false;
        if let Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(needed_left, needed_right),
            true,
        ) = &self.goal
            && let Some((needed_memory, needed_pointer)) = traced_read(needed_left)
        {
            let needed_snapshot = labels.snapshot_name(needed_memory.memory());
            for fact in &self.available {
                let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                    fact
                else {
                    continue;
                };
                let Some((known_memory, known_pointer)) = traced_read(left) else {
                    continue;
                };
                if known_pointer == needed_pointer && right == needed_right {
                    relevant.push(fact);
                    if known_memory != needed_memory {
                        different_snapshots = true;
                        output.push_str(&format!(
                            "\n    same address and required value: known at {}, needed at {}",
                            labels.snapshot_name(known_memory.memory()),
                            needed_snapshot,
                        ));
                    }
                }
            }
            if different_snapshots {
                output.push_str(
                    "\n    certification did not establish that these snapshot reads agree",
                );
            }
        }
        if relevant.is_empty() {
            relevant.extend(self.available.iter().take(8));
        }
        let shown = relevant.len();
        output.push_str(&format!(
            "\n    checked facts (showing {} of {}):",
            shown, self.available_count,
        ));
        for fact in relevant {
            let source = render::render_simple_click_fact_labeled(fact, labels);
            let description = source.unwrap_or_else(|| {
                format!(
                    "internal fact (no exact Click spelling): {}",
                    render::render_proposition_labeled(fact, labels)
                )
            });
            let description = trace_text(&description, 512);
            if output.len() + description.len() > MAX_RENDER_BYTES {
                output.push_str("\n    … <trace output limit reached>");
                break;
            }
            output.push_str("\n    fact: ");
            output.push_str(&description);
        }
        if shown < self.available_count {
            output.push_str("\n    … <other available facts omitted>");
        }
        Some(output)
    }
}

thread_local! {
    static CAPTURE: RefCell<Option<Capture>> = const { RefCell::new(None) };
}

/// Scope tracing to one named function on the verification thread.
pub fn with_proof_trace<R>(function: &str, verify: impl FnOnce() -> R) -> R {
    struct Restore(Option<Capture>);
    impl Drop for Restore {
        fn drop(&mut self) {
            CAPTURE.with(|slot| *slot.borrow_mut() = self.0.take());
        }
    }
    let prior = CAPTURE.with(|slot| {
        slot.replace(Some(Capture {
            function: function.to_owned(),
            steps: HashMap::new(),
            branches: HashMap::new(),
            joins: HashMap::new(),
            bodies: HashMap::new(),
            scope_parents: HashMap::new(),
            limit_reached: false,
        }))
    });
    let _restore = Restore(prior);
    verify()
}

pub(super) fn enabled_for(claim: &str) -> bool {
    CAPTURE.with(|slot| {
        slot.borrow().as_ref().is_some_and(|capture| {
            claim
                .strip_prefix(&capture.function)
                .is_some_and(|tail| tail.starts_with('.') || tail.is_empty())
        })
    })
}

pub(super) fn record(node: usize, step: TraceStep) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.steps.len() < MAX_STEPS {
            capture.steps.insert(node, step);
        } else {
            capture.limit_reached = true;
        }
    });
}

pub(super) fn record_branch(node: usize, branch: TraceBranch) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.branches.len() < MAX_STEPS {
            capture.branches.insert(node, branch);
        } else {
            capture.limit_reached = true;
        }
    });
}

pub(super) fn record_join(node: usize, join: TraceJoin) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.joins.len() < MAX_STEPS {
            capture.joins.insert(node, join);
        } else {
            capture.limit_reached = true;
        }
    });
}

pub(super) fn record_body(node: usize, body: TraceBody) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.bodies.len() < MAX_STEPS {
            capture.bodies.insert(node, body);
        } else {
            capture.limit_reached = true;
        }
    });
}

pub(super) fn register_scope(
    root: usize,
    parent_lineage: Vec<TracePathNode>,
    retained: Box<dyn Any>,
) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.scope_parents.len() < MAX_STEPS {
            capture.scope_parents.insert(
                root,
                TraceScope {
                    lineage: parent_lineage,
                    _retained: retained,
                },
            );
        } else {
            capture.limit_reached = true;
        }
    });
}

/// Walk the accepted proof lineage. A structural join carries the checked
/// arm lineages it replaced, so an earlier call remains visible without
/// including abandoned smart-search candidates.
pub(super) fn render(
    claim: &str,
    lineage: &[TracePathNode],
    labels: &mut SnapshotLabels,
) -> Option<String> {
    CAPTURE.with(|slot| {
        let slot = slot.borrow();
        let capture = slot.as_ref()?;
        if !enabled_for(claim) {
            return None;
        }
        let mut output = String::from("  proof trace (checked tactics and branch facts):");
        let mut segments = vec![lineage];
        while segments.len() < MAX_STEPS {
            let Some(root) = segments.last().and_then(|segment| segment.first()) else {
                break;
            };
            let Some(parent) = capture.scope_parents.get(&root.node) else {
                break;
            };
            segments.push(&parent.lineage);
        }
        let mut shown = 0;
        let mut depth = 0;
        for segment in segments.into_iter().rev() {
            depth = append_path(&mut output, capture, segment, labels, depth, &mut shown);
        }
        if shown == 0 {
            output.push_str("\n    <no checked simple steps recorded on this path>");
        }
        if capture.limit_reached {
            output.push_str("\n    … <trace step limit reached; later steps omitted>");
        }
        Some(output)
    })
}

fn append_path(
    output: &mut String,
    capture: &Capture,
    lineage: &[TracePathNode],
    labels: &mut SnapshotLabels,
    mut depth: usize,
    shown: &mut usize,
) -> usize {
    if depth > 64 || *shown >= MAX_STEPS || output.len() >= MAX_RENDER_BYTES {
        return depth;
    }
    for path_node in lineage {
        let indent = " ".repeat(2 + depth * 2);
        let mut detail = String::new();
        if let Some(join) = capture.joins.get(&path_node.node) {
            if let Some(branch) = capture.branches.get(&join.marker) {
                detail.push_str(&format!("\n{indent}{}", branch.header));
                output.push_str(&detail);
                *shown += 1;
                for arm in 0..2 {
                    let arm_indent = " ".repeat(4 + depth * 2);
                    let mut arm_detail = format!(
                        "\n{arm_indent}{} arm:",
                        if arm == 0 { "then" } else { "else" }
                    );
                    append_added_facts(
                        &mut arm_detail,
                        &branch.arms[arm].1,
                        labels,
                        &format!("{arm_indent}  "),
                    );
                    output.push_str(&arm_detail);
                    append_path(output, capture, &join.arms[arm], labels, depth + 2, shown);
                }
            }
            continue;
        }
        if let (Some(branch), Some(selected_arm)) = (
            capture.branches.get(&path_node.node),
            path_node.selected_arm,
        ) {
            let Some((arm, (_, facts))) = branch
                .arms
                .iter()
                .enumerate()
                .find(|(_, (id, _))| *id == selected_arm)
            else {
                continue;
            };
            detail.push_str(&format!("\n{indent}{}", branch.header));
            detail.push_str(&format!(
                "\n{indent}  {} arm:",
                if arm == 0 { "then" } else { "else" }
            ));
            append_added_facts(&mut detail, facts, labels, &format!("{indent}    "));
            depth += 2;
        } else if let Some(step) = capture.steps.get(&path_node.node) {
            detail.push_str(&format!(
                "\n{indent}{}",
                trace_text(step.header.trim(), 240)
            ));
            let detail_indent = format!("{indent}  ");
            if let Some(call) = &step.call_source {
                for guarantee in &call.guarantees {
                    detail.push_str(&format!(
                        "\n{detail_indent}ensures (source template): {}",
                        trace_text(guarantee, 240)
                    ));
                }
                if call.more_guarantees > 0 {
                    detail.push_str(&format!(
                        "\n{detail_indent}… {} more source guarantees",
                        call.more_guarantees
                    ));
                }
            }
            append_added_facts(&mut detail, &step.facts, labels, &detail_indent);
            if step.more_facts > 0 {
                detail.push_str(&format!(
                    "\n{detail_indent}… {} more added facts",
                    step.more_facts
                ));
            }
            if let Some(frontier) = &step.frontier {
                detail.push_str(&format!("\n{detail_indent}C frontier: {frontier}"));
            }
            let resource_changes = step.resources.len() + step.more_resources;
            if resource_changes > 0 {
                detail.push_str(&format!(
                    "\n{detail_indent}resource changes: {resource_changes}"
                ));
            }
        } else {
            continue;
        }
        if output.len() + detail.len() > MAX_RENDER_BYTES {
            output.push_str("\n    … <trace output limit reached>");
            break;
        }
        output.push_str(&detail);
        *shown += 1;
        if let Some(body) = capture.bodies.get(&path_node.node) {
            append_path(output, capture, &body.lineage, labels, depth + 1, shown);
        }
    }
    depth
}

fn append_added_facts(
    output: &mut String,
    facts: &[TraceFact],
    labels: &mut SnapshotLabels,
    indent: &str,
) {
    let mut unspelled = 0;
    for fact in facts {
        let source = fact
            .source
            .clone()
            .or_else(|| render::render_simple_click_fact_labeled(&fact.kernel, labels));
        if let Some(source) = source {
            output.push_str(&format!("\n{indent}adds: {}", trace_text(&source, 240)));
        } else {
            unspelled += 1;
        }
    }
    if unspelled > 0 {
        output.push_str(&format!(
            "\n{indent}adds: {unspelled} checked fact(s) with no exact Click spelling"
        ));
    }
}

fn trace_text(text: &str, max_bytes: usize) -> String {
    if text.len() <= max_bytes {
        return text.to_owned();
    }
    let mut end = max_bytes.saturating_sub('…'.len_utf8());
    while end > 0 && !text.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}…", &text[..end])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{Bitvector32Term, CMemory, Pointer, PointerBlock, PointerOffsetTerm};

    fn loadable_at(memory: CMemory) -> Proposition {
        Proposition::CMemoryLoadable {
            memory,
            base: Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(1),
        }
    }

    #[test]
    fn trace_and_goal_share_snapshot_labels_without_conflating_distinct_memories() {
        with_proof_trace("f", || {
            let first = CMemory::default();
            let second = CMemory::new().with_block("different", 1);
            record(
                1,
                TraceStep {
                    header: "\n    source tactic 0: step".into(),
                    call_source: None,
                    facts: vec![
                        TraceFact {
                            kernel: loadable_at(first.clone()),
                            source: None,
                        },
                        TraceFact {
                            kernel: loadable_at(second.clone()),
                            source: None,
                        },
                    ],
                    more_facts: 0,
                    frontier: None,
                    resources: Vec::new(),
                    more_resources: 0,
                },
            );
            let mut labels = SnapshotLabels::default();
            let goal = render::render_proposition_labeled(&loadable_at(first), &mut labels);
            let trace = render(
                "f",
                &[TracePathNode {
                    node: 1,
                    selected_arm: None,
                }],
                &mut labels,
            )
            .unwrap();
            assert!(goal.contains("snapshot#1"), "{goal}");
            assert!(
                trace.contains("adds: 2 checked fact(s) with no exact Click spelling"),
                "{trace}"
            );
            assert!(!trace.contains("snapshot#2"), "{trace}");
        });
    }

    #[test]
    fn nested_scope_trace_keeps_the_enclosing_checked_step() {
        with_proof_trace("f", || {
            let step = |header| TraceStep {
                header,
                call_source: None,
                facts: Vec::new(),
                more_facts: 0,
                frontier: None,
                resources: Vec::new(),
                more_resources: 0,
            };
            record(1, step("\n    source tactic 0: step".into()));
            record(3, step("\n    have body tactic 0: normalize".into()));
            register_scope(
                2,
                vec![TracePathNode {
                    node: 1,
                    selected_arm: None,
                }],
                Box::new(()),
            );
            let trace = render(
                "f",
                &[
                    TracePathNode {
                        node: 2,
                        selected_arm: None,
                    },
                    TracePathNode {
                        node: 3,
                        selected_arm: None,
                    },
                ],
                &mut SnapshotLabels::default(),
            )
            .unwrap();
            assert!(trace.contains("source tactic 0: step"), "{trace}");
            assert!(trace.contains("have body tactic 0: normalize"), "{trace}");
        });
    }

    #[test]
    fn exact_click_fact_takes_precedence_over_internal_rendering() {
        with_proof_trace("f", || {
            record(
                1,
                TraceStep {
                    header: "\n    source tactic 0: have".into(),
                    call_source: None,
                    facts: vec![TraceFact {
                        kernel: Proposition::ConditionIs(
                            crate::kernel::ConditionTerm::Constant(true),
                            true,
                        ),
                        source: Some("x == x".into()),
                    }],
                    more_facts: 0,
                    frontier: None,
                    resources: Vec::new(),
                    more_resources: 0,
                },
            );
            let report = render(
                "f",
                &[TracePathNode {
                    node: 1,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
            )
            .unwrap();
            assert!(report.contains("adds: x == x"), "{report}");
            assert!(!report.contains("no exact Click spelling"), "{report}");
        });
    }

    #[test]
    fn joined_branch_retains_only_accepted_arm_steps() {
        with_proof_trace("f", || {
            let step = |name: &str| TraceStep {
                header: format!("source tactic: {name}"),
                call_source: None,
                facts: Vec::new(),
                more_facts: 0,
                frontier: None,
                resources: Vec::new(),
                more_resources: 0,
            };
            record(2, step("then step"));
            record(3, step("else step"));
            record(4, step("discarded candidate"));
            record_branch(
                1,
                TraceBranch {
                    header: "source tactic 0: branch".into(),
                    arms: [
                        (
                            BranchId::ROOT,
                            vec![TraceFact {
                                kernel: Proposition::ConditionIs(
                                    ConditionTerm::Constant(true),
                                    true,
                                ),
                                source: Some("x != 0".into()),
                            }],
                        ),
                        (
                            BranchId::ROOT,
                            vec![TraceFact {
                                kernel: Proposition::ConditionIs(
                                    ConditionTerm::Constant(false),
                                    false,
                                ),
                                source: Some("x == 0".into()),
                            }],
                        ),
                    ],
                },
            );
            record_join(
                5,
                TraceJoin {
                    marker: 1,
                    arms: [
                        vec![TracePathNode {
                            node: 2,
                            selected_arm: None,
                        }],
                        vec![TracePathNode {
                            node: 3,
                            selected_arm: None,
                        }],
                    ],
                    _retained: Box::new(()),
                },
            );
            let trace = render(
                "f",
                &[TracePathNode {
                    node: 5,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
            )
            .unwrap();
            assert!(trace.contains("adds: x != 0"), "{trace}");
            assert!(trace.contains("adds: x == 0"), "{trace}");
            assert!(trace.contains("then step"), "{trace}");
            assert!(trace.contains("else step"), "{trace}");
            assert!(!trace.contains("discarded candidate"), "{trace}");
        });
    }

    #[test]
    fn completed_have_shows_its_fact_and_body_tactics() {
        with_proof_trace("f", || {
            let fact = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
            record(
                1,
                TraceStep {
                    header: "source tactic 2: have x == x".into(),
                    call_source: None,
                    facts: vec![TraceFact {
                        kernel: fact,
                        source: Some("x == x".into()),
                    }],
                    more_facts: 0,
                    frontier: None,
                    resources: Vec::new(),
                    more_resources: 0,
                },
            );
            record(
                2,
                TraceStep {
                    header: "have body tactic 1: normalize()".into(),
                    call_source: None,
                    facts: Vec::new(),
                    more_facts: 0,
                    frontier: None,
                    resources: Vec::new(),
                    more_resources: 0,
                },
            );
            record_body(
                1,
                TraceBody {
                    lineage: vec![TracePathNode {
                        node: 2,
                        selected_arm: None,
                    }],
                    _retained: Box::new(()),
                },
            );
            let report = render(
                "f",
                &[TracePathNode {
                    node: 1,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
            )
            .unwrap();
            assert!(report.contains("source tactic 2: have x == x"), "{report}");
            assert!(report.contains("adds: x == x"), "{report}");
            assert!(
                report.contains("have body tactic 1: normalize()"),
                "{report}"
            );
        });
    }
}
