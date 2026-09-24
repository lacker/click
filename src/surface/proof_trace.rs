//! Opt-in, bounded observations of checked proof steps for CLI diagnostics.
//! The trace is diagnostic only; no recorded text participates in checking.

use crate::kernel::ContractPathPreparationFailure;
use crate::kernel::proof::BranchId;
use crate::kernel::{Bitvector32Term, ConditionTerm, Pointer, Proposition, SharedCMemory};
use crate::source::SourcePosition;
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
    accepted_paths: Vec<TraceAcceptedPath>,
    limit_reached: bool,
}

struct TraceAcceptedPath {
    claim: String,
    path_index: usize,
    lineage: Vec<TracePathNode>,
    /// Retain the accepted provenance chain until the CLI has rendered it.
    _retained: Box<dyn Any>,
}

#[derive(Clone, Copy)]
pub(super) struct TracePathNode {
    pub node: usize,
    pub selected_arm: Option<BranchId>,
}

pub(super) struct TraceJoin {
    pub marker: usize,
    pub arms: [Vec<TracePathNode>; 2],
    pub facts: Vec<TraceFact>,
    pub more_facts: usize,
    /// One arm ran the source continuation before a terminal join.
    pub continuation_arm: Option<usize>,
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
    pub source_tactic_path: Option<Vec<usize>>,
    pub arms: [(BranchId, Vec<TraceFact>); 2],
}

pub(super) struct TraceStep {
    pub header: String,
    pub source_tactic_path: Option<Vec<usize>>,
    pub call_source: Option<TraceCallSource>,
    pub facts: Vec<TraceFact>,
    pub more_facts: usize,
    pub frontier: Option<String>,
    pub resources: Vec<TraceResourceChange>,
    pub more_resources: usize,
}

pub(super) struct TraceResourceChange {
    pub before: usize,
    pub after: usize,
    pub description: String,
}

pub(super) struct TraceCallSource {
    pub call: String,
}

pub(super) struct TraceFact {
    pub kernel: Proposition,
    /// A form re-lowered to this exact fact at the checked step.
    pub source: Option<String>,
    /// A structural, source-facing rendering of the checked kernel fact.
    /// Unlike `source`, this is presentation, not a validated citation.
    pub surface_view: Option<String>,
}

/// The generated equation connecting a canonical load value to its raw
/// memory read is checker bookkeeping, not an additional surface premise.
/// The surface condition that caused the read is reported separately.
pub(super) fn visible_checked_fact(fact: &Proposition) -> bool {
    !crate::kernel::is_load_variable_defining_fact(fact)
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

    fn proof_trace(
        &self,
        _claim: &str,
        labels: &mut SnapshotLabels,
        _tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
        _branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
        _have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
        _target: Option<&SourcePosition>,
    ) -> Option<String> {
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
            accepted_paths: Vec::new(),
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

pub(super) fn set_join_continuation_arm(node: usize, arm: usize) {
    CAPTURE.with(|slot| {
        if let Some(join) = slot
            .borrow_mut()
            .as_mut()
            .and_then(|capture| capture.joins.get_mut(&node))
        {
            join.continuation_arm = Some(arm);
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

pub(super) fn record_accepted_path(
    claim: &str,
    path_index: usize,
    lineage: Vec<TracePathNode>,
    retained: Box<dyn Any>,
) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.accepted_paths.len() < MAX_STEPS {
            capture.accepted_paths.push(TraceAcceptedPath {
                claim: claim.to_owned(),
                path_index,
                lineage,
                _retained: retained,
            });
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
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
) -> Option<String> {
    CAPTURE.with(|slot| {
        let slot = slot.borrow();
        let capture = slot.as_ref()?;
        if !enabled_for(claim) {
            return None;
        }
        Some(
            render_lineage(
                capture,
                lineage,
                labels,
                tactic_location,
                branch_arm,
                have_body_contains,
                target,
            )
            .0,
        )
    })
}

/// Render a completed proof only from paths retained after checked path
/// certification. A target inside one path selects that path; without a
/// target, the first accepted path is a representative execution route.
pub(crate) fn render_accepted(
    labels: &mut SnapshotLabels,
    tactic_location: &dyn Fn(&str, &[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&str, &[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&str, &[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
) -> Option<String> {
    CAPTURE.with(|slot| {
        let slot = slot.borrow();
        let capture = slot.as_ref()?;
        for path in &capture.accepted_paths {
            let locate = |indices: &[usize]| tactic_location(&path.claim, indices);
            let arm = |indices: &[usize], position: &SourcePosition| {
                branch_arm(&path.claim, indices, position)
            };
            let body = |indices: &[usize], position: &SourcePosition| {
                have_body_contains(&path.claim, indices, position)
            };
            let mut path_labels = SnapshotLabels::default();
            let (mut report, reached) = render_lineage(
                capture,
                &path.lineage,
                &mut path_labels,
                &locate,
                &arm,
                &body,
                target,
            );
            if target.is_none() || reached {
                *labels = path_labels;
                if capture.accepted_paths.len() > 1 {
                    report = report.replacen(
                        "proof trace (checked tactics and branch facts)",
                        &format!("proof trace (accepted path {})", path.path_index),
                        1,
                    );
                }
                return Some(report);
            }
        }
        None
    })
}

fn render_lineage(
    capture: &Capture,
    lineage: &[TracePathNode],
    labels: &mut SnapshotLabels,
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
) -> (String, bool) {
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
    let mut done = false;
    let mut reached = false;
    for segment in segments.into_iter().rev() {
        depth = append_path(
            &mut output,
            capture,
            segment,
            labels,
            tactic_location,
            branch_arm,
            have_body_contains,
            target,
            depth,
            &mut shown,
            &mut done,
            &mut reached,
        );
        if done {
            break;
        }
    }
    if shown == 0 {
        output.push_str("\n    <no checked simple steps recorded on this path>");
    }
    if capture.limit_reached {
        output.push_str("\n    … <trace step limit reached; later steps omitted>");
    }
    (output, reached)
}

fn append_path(
    output: &mut String,
    capture: &Capture,
    lineage: &[TracePathNode],
    labels: &mut SnapshotLabels,
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
    mut depth: usize,
    shown: &mut usize,
    done: &mut bool,
    reached: &mut bool,
) -> usize {
    if depth > 64 || *shown >= MAX_STEPS || output.len() >= MAX_RENDER_BYTES {
        return depth;
    }
    for path_node in lineage {
        if *done {
            break;
        }
        let indent = " ".repeat(2 + depth * 2);
        let mut detail = String::new();
        if let Some(join) = capture.joins.get(&path_node.node) {
            if let Some(branch) = capture.branches.get(&join.marker) {
                let site = branch
                    .source_tactic_path
                    .as_deref()
                    .and_then(tactic_location);
                if target.is_some_and(|target| {
                    site.as_ref()
                        .is_some_and(|(_, at)| source_after(at, target))
                }) {
                    *done = true;
                    break;
                }
                let header = trace_header(
                    &branch.header,
                    branch.source_tactic_path.as_deref(),
                    tactic_location,
                );
                let selected_arm = target
                    .and_then(|target| {
                        branch
                            .source_tactic_path
                            .as_deref()
                            .and_then(|path| branch_arm(path, target))
                    })
                    .or_else(|| {
                        target.and_then(|target| {
                            site.as_ref()
                                .is_some_and(|(_, at)| source_after(target, at))
                                .then_some(join.continuation_arm)
                                .flatten()
                        })
                    });
                if let Some(arm) = selected_arm {
                    detail.push_str(&format!(
                        "\n{indent}{header} ({} arm)",
                        if arm == 0 { "then" } else { "else" }
                    ));
                    append_added_facts(
                        &mut detail,
                        &branch.arms[arm].1,
                        labels,
                        &format!("{indent}  "),
                    );
                    if output.len() + detail.len() > MAX_RENDER_BYTES {
                        output.push_str("\n    … <trace output limit reached>");
                        *done = true;
                        break;
                    }
                    output.push_str(&detail);
                    *shown += 1;
                    append_path(
                        output,
                        capture,
                        &join.arms[arm],
                        labels,
                        tactic_location,
                        branch_arm,
                        have_body_contains,
                        target,
                        depth + 1,
                        shown,
                        done,
                        reached,
                    );
                    *done = true;
                } else {
                    detail.push_str(&format!("\n{indent}{header}"));
                    append_added_facts(&mut detail, &join.facts, labels, &format!("{indent}  "));
                    if join.more_facts > 0 {
                        detail.push_str(&format!(
                            "\n{indent}  … {} more joined facts",
                            join.more_facts
                        ));
                    }
                    if output.len() + detail.len() > MAX_RENDER_BYTES {
                        output.push_str("\n    … <trace output limit reached>");
                        *done = true;
                        break;
                    }
                    output.push_str(&detail);
                    *shown += 1;
                    if target.is_some_and(|target| {
                        site.as_ref().is_some_and(|(_, at)| source_same(at, target))
                    }) {
                        *reached = true;
                    }
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
            let site = branch
                .source_tactic_path
                .as_deref()
                .and_then(tactic_location);
            if target.is_some_and(|target| {
                site.as_ref()
                    .is_some_and(|(_, at)| source_after(at, target))
            }) {
                *done = true;
                break;
            }
            detail.push_str(&format!(
                "\n{indent}{} ({} arm)",
                trace_header(
                    &branch.header,
                    branch.source_tactic_path.as_deref(),
                    tactic_location,
                ),
                if arm == 0 { "then" } else { "else" },
            ));
            append_added_facts(&mut detail, facts, labels, &format!("{indent}  "));
            depth += 1;
        } else if let Some(step) = capture.steps.get(&path_node.node) {
            if step
                .header
                .trim()
                .rsplit_once(": ")
                .is_some_and(|(_, kind)| kind == "mark")
            {
                continue;
            }
            let site = step.source_tactic_path.as_deref().and_then(tactic_location);
            if target.is_some_and(|target| {
                site.as_ref()
                    .is_some_and(|(_, at)| source_after(at, target))
            }) {
                *done = true;
                break;
            }
            detail.push_str(&format!(
                "\n{indent}{}",
                trace_text(
                    &trace_header(
                        step.header.trim(),
                        step.source_tactic_path.as_deref(),
                        tactic_location,
                    ),
                    240
                )
            ));
            let detail_indent = format!("{indent}  ");
            append_added_facts(&mut detail, &step.facts, labels, &detail_indent);
            if step.more_facts > 0 {
                detail.push_str(&format!(
                    "\n{detail_indent}… {} more added facts",
                    step.more_facts
                ));
            }
            if let Some(frontier) = &step.frontier {
                detail.push_str(&format!("\n{detail_indent}{}", trace_text(frontier, 240)));
            }
            for resource in &step.resources {
                let change = match (resource.before, resource.after) {
                    (0, 1) => format!("resource gained: {}", resource.description),
                    (1, 0) => format!("resource lost: {}", resource.description),
                    _ => format!(
                        "resource count: {} ({} -> {})",
                        resource.description, resource.before, resource.after
                    ),
                };
                detail.push_str(&format!("\n{detail_indent}{}", trace_text(&change, 240)));
            }
            if step.more_resources > 0 {
                detail.push_str(&format!(
                    "\n{detail_indent}… {} more resource changes",
                    step.more_resources
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
        if let Some(target) = target {
            let path = capture
                .steps
                .get(&path_node.node)
                .and_then(|step| step.source_tactic_path.as_deref())
                .or_else(|| {
                    capture
                        .branches
                        .get(&path_node.node)
                        .and_then(|branch| branch.source_tactic_path.as_deref())
                });
            if path
                .and_then(tactic_location)
                .is_some_and(|(_, at)| source_same(&at, target))
            {
                *reached = true;
            }
        }
        if let Some(body) = capture.bodies.get(&path_node.node)
            && target.is_some_and(|target| {
                capture
                    .steps
                    .get(&path_node.node)
                    .and_then(|step| step.source_tactic_path.as_deref())
                    .is_some_and(|path| have_body_contains(path, target))
            })
        {
            if *done {
                break;
            }
            append_path(
                output,
                capture,
                &body.lineage,
                labels,
                tactic_location,
                branch_arm,
                have_body_contains,
                target,
                depth + 1,
                shown,
                done,
                reached,
            );
        }
    }
    depth
}

fn trace_header(
    header: &str,
    path: Option<&[usize]>,
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
) -> String {
    let Some((location, _)) = path.and_then(tactic_location) else {
        return header.to_owned();
    };
    let Some((_, description)) = header.trim().split_once(": ") else {
        return header.to_owned();
    };
    format!("{location}: {description}")
}

fn source_after(position: &SourcePosition, target: &SourcePosition) -> bool {
    (position.line, position.column) > (target.line, target.column)
}

fn source_same(position: &SourcePosition, target: &SourcePosition) -> bool {
    (position.line, position.column) == (target.line, target.column)
}

fn append_added_facts(
    output: &mut String,
    facts: &[TraceFact],
    labels: &mut SnapshotLabels,
    indent: &str,
) {
    let mut unspelled = 0;
    for fact in facts {
        if !visible_checked_fact(&fact.kernel) {
            continue;
        }
        let source = fact
            .source
            .clone()
            .or_else(|| render::render_simple_click_fact_labeled(&fact.kernel, labels));
        if let Some(source) = source {
            output.push_str(&format!("\n{indent}adds: {}", trace_text(&source, 240)));
        } else if let Some(surface) = &fact.surface_view {
            output.push_str(&format!(
                "\n{indent}adds (surface view): {}",
                trace_text(surface, 240)
            ));
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

    #[test]
    fn trace_header_uses_resolved_source_tactic_location() {
        let label = |path: &[usize]| {
            (path == [3, 1]).then(|| ("tactic@475".to_owned(), SourcePosition::new(475, 1)))
        };
        assert_eq!(
            trace_header(
                "tactic 3 > have body tactic 1: assumption()",
                Some(&[3, 1]),
                &label,
            ),
            "tactic@475: assumption()"
        );
    }

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
                    source_tactic_path: None,
                    call_source: None,
                    facts: vec![
                        TraceFact {
                            kernel: loadable_at(first.clone()),
                            source: None,
                            surface_view: None,
                        },
                        TraceFact {
                            kernel: loadable_at(second.clone()),
                            source: None,
                            surface_view: None,
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
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
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
                source_tactic_path: None,
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
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
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
                    source_tactic_path: None,
                    call_source: None,
                    facts: vec![TraceFact {
                        kernel: Proposition::ConditionIs(
                            crate::kernel::ConditionTerm::Constant(true),
                            true,
                        ),
                        source: Some("x == x".into()),
                        surface_view: Some("different rendering".into()),
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
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
            )
            .unwrap();
            assert!(report.contains("adds: x == x"), "{report}");
            assert!(!report.contains("different rendering"), "{report}");
            assert!(!report.contains("no exact Click spelling"), "{report}");
        });
    }

    #[test]
    fn trace_prints_surface_view_when_exact_citation_is_unavailable() {
        let mut output = String::new();
        append_added_facts(
            &mut output,
            &[TraceFact {
                kernel: Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                source: None,
                surface_view: Some("0 <= unmarked(visited, 0, n)".into()),
            }],
            &mut SnapshotLabels::default(),
            "  ",
        );
        assert_eq!(
            output,
            "\n  adds (surface view): 0 <= unmarked(visited, 0, n)"
        );
    }

    #[test]
    fn trace_omits_generated_load_binding_beside_surface_branch_fact() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let Bitvector32Term::Variable(variable) =
            crate::kernel::canonical_form_of_load(memory.clone(), pointer.clone())
        else {
            panic!("an unresolved external read has a load variable");
        };
        let defining = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(Bitvector32Term::MemoryLoad(memory, Box::new(pointer))),
            ),
            true,
        );
        let mut output = String::new();
        append_added_facts(
            &mut output,
            &[
                TraceFact {
                    kernel: Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                    source: Some("at(statement(0).entry, visited[cur]) == 0".into()),
                    surface_view: None,
                },
                TraceFact {
                    kernel: defining,
                    source: None,
                    surface_view: None,
                },
            ],
            &mut SnapshotLabels::default(),
            "  ",
        );
        assert_eq!(
            output,
            "\n  adds: at(statement(0).entry, visited[cur]) == 0"
        );
    }

    #[test]
    fn joined_branch_retains_only_accepted_arm_steps() {
        with_proof_trace("f", || {
            let step = |name: &str| TraceStep {
                header: format!("source tactic: {name}"),
                source_tactic_path: None,
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
                    source_tactic_path: Some(vec![0]),
                    arms: [
                        (
                            BranchId::ROOT,
                            vec![TraceFact {
                                kernel: Proposition::ConditionIs(
                                    ConditionTerm::Constant(true),
                                    true,
                                ),
                                source: Some("x != 0".into()),
                                surface_view: None,
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
                                surface_view: None,
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
                    facts: vec![TraceFact {
                        kernel: Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                        source: Some("stable".into()),
                        surface_view: None,
                    }],
                    more_facts: 0,
                    continuation_arm: None,
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
                &|_| Some(("tactic@1".into(), SourcePosition::new(1, 1))),
                &|_, _| Some(0),
                &|_, _| false,
                Some(&SourcePosition::new(2, 1)),
            )
            .unwrap();
            assert!(trace.contains("tactic@1: branch (then arm)"), "{trace}");
            assert!(trace.contains("adds: x != 0"), "{trace}");
            assert!(trace.contains("then step"), "{trace}");
            assert!(!trace.contains("adds: x == 0"), "{trace}");
            assert!(!trace.contains("else step"), "{trace}");
            assert!(!trace.contains("discarded candidate"), "{trace}");
            let summary = render(
                "f",
                &[TracePathNode {
                    node: 5,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
                &|_| Some(("tactic@1".into(), SourcePosition::new(1, 1))),
                &|_, _| None,
                &|_, _| false,
                Some(&SourcePosition::new(3, 1)),
            )
            .unwrap();
            assert!(summary.contains("adds: stable"), "{summary}");
            assert!(!summary.contains("then step"), "{summary}");
            assert!(!summary.contains("else step"), "{summary}");
        });
    }

    #[test]
    fn completed_have_shows_only_its_exported_fact_unless_target_is_inside() {
        with_proof_trace("f", || {
            let fact = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
            record(
                1,
                TraceStep {
                    header: "source tactic 2: have x == x".into(),
                    source_tactic_path: Some(vec![2]),
                    call_source: None,
                    facts: vec![TraceFact {
                        kernel: fact,
                        source: Some("x == x".into()),
                        surface_view: None,
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
                    source_tactic_path: Some(vec![2, 1]),
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
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
            )
            .unwrap();
            assert!(report.contains("source tactic 2: have x == x"), "{report}");
            assert!(report.contains("adds: x == x"), "{report}");
            assert!(
                !report.contains("have body tactic 1: normalize()"),
                "{report}"
            );
            let inside = render(
                "f",
                &[TracePathNode {
                    node: 1,
                    selected_arm: None,
                }],
                &mut SnapshotLabels::default(),
                &|path| match path {
                    [2] => Some(("tactic@2".into(), SourcePosition::new(2, 1))),
                    [2, 1] => Some(("tactic@3".into(), SourcePosition::new(3, 1))),
                    _ => None,
                },
                &|_, _| None,
                &|path, _| path == [2],
                Some(&SourcePosition::new(3, 1)),
            )
            .unwrap();
            assert!(inside.contains("tactic@3: normalize()"), "{inside}");
        });
    }

    #[test]
    fn successful_trace_uses_only_retained_accepted_lineage() {
        with_proof_trace("f", || {
            let step = |header| TraceStep {
                header,
                source_tactic_path: None,
                call_source: None,
                facts: Vec::new(),
                more_facts: 0,
                frontier: None,
                resources: Vec::new(),
                more_resources: 0,
            };
            record(1, step("source tactic 0: accepted".into()));
            record(2, step("source tactic 0: abandoned candidate".into()));
            record(3, step("source tactic 0: mark".into()));
            record_accepted_path(
                "f.contract",
                0,
                vec![
                    TracePathNode {
                        node: 3,
                        selected_arm: None,
                    },
                    TracePathNode {
                        node: 1,
                        selected_arm: None,
                    },
                ],
                Box::new(()),
            );
            let report = render_accepted(
                &mut SnapshotLabels::default(),
                &|_, _| None,
                &|_, _, _| None,
                &|_, _, _| false,
                None,
            )
            .unwrap();
            assert!(report.contains("accepted"), "{report}");
            assert!(!report.contains("abandoned candidate"), "{report}");
            assert!(!report.contains(": mark"), "{report}");
        });
    }
}
