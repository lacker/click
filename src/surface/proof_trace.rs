//! Opt-in, bounded observations of checked proof steps for CLI diagnostics.
//! The trace is diagnostic only; no recorded text participates in checking.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::kernel::{CResourceFact, Proposition};
use crate::surface::proof_diagnostics::render::{self, SnapshotLabels};

pub(super) const MAX_STEPS: usize = 2048;
const MAX_RENDER_BYTES: usize = 64 * 1024;

struct Capture {
    function: String,
    steps: HashMap<usize, TraceStep>,
    scope_parents: HashMap<usize, Vec<usize>>,
    limit_reached: bool,
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
    pub arguments: Vec<(String, String)>,
    pub guarantees: Vec<String>,
    pub more_guarantees: usize,
}

pub(super) struct TraceFact {
    pub kernel: Proposition,
    /// A form re-lowered to this exact fact at the checked step. A generated
    /// fact without such a form remains explicitly internal in the report.
    pub source: Option<String>,
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

/// Link a fresh scoped proof root to the checked enclosing path. Proof scopes
/// intentionally have independent certificate roots, so their normal node
/// lineage alone cannot explain an earlier call when a nested `have` fails.
pub(super) fn register_scope(root: usize, parent_lineage: Vec<usize>) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        if capture.scope_parents.len() < MAX_STEPS {
            capture.scope_parents.insert(root, parent_lineage);
        } else {
            capture.limit_reached = true;
        }
    });
}

/// Render only nodes on the failing proof's lineage. Discarded smart-search
/// candidates may have been checked but never appear on this path.
pub(super) fn render(
    claim: &str,
    lineage: &[usize],
    labels: &mut SnapshotLabels,
) -> Option<String> {
    CAPTURE.with(|slot| {
        let slot = slot.borrow();
        let capture = slot.as_ref()?;
        if !enabled_for(claim) {
            return None;
        }
        let mut output = String::from(
            "  proof trace (checked steps on the failing path):\n    snapshot# labels are shared with this report's goal and premises; snapshot<untracked> has unknown identity",
        );
        let mut segments = vec![lineage];
        while segments.len() < MAX_STEPS {
            let Some(root) = segments.last().and_then(|segment| segment.first()) else {
                break;
            };
            let Some(parent) = capture.scope_parents.get(root) else {
                break;
            };
            segments.push(parent);
        }
        let mut shown = 0;
        for node in segments.into_iter().rev().flatten() {
            let Some(step) = capture.steps.get(node) else {
                continue;
            };
            let mut detail = step.header.clone();
            if let Some(call) = &step.call_source {
                detail.push_str("\n      source call: ");
                detail.push_str(&trace_text(&call.call, 240));
                for (parameter, argument) in &call.arguments {
                    detail.push_str("\n      argument ");
                    detail.push_str(&trace_text(parameter, 60));
                    detail.push_str(" = ");
                    detail.push_str(&trace_text(argument, 160));
                }
                for guarantee in &call.guarantees {
                    detail.push_str("\n      callee ensures (source template): ");
                    detail.push_str(&trace_text(guarantee, 240));
                }
                if call.more_guarantees > 0 {
                    detail.push_str(&format!(
                        "\n      … {} more source guarantees",
                        call.more_guarantees
                    ));
                }
            }
            let mut unspelled = 0;
            let mut unspelled_snapshots = Vec::new();
            for fact in &step.facts {
                if let Some(source) = fact.source.as_ref() {
                    detail.push_str("\n      fact + ");
                    detail.push_str(&trace_text(source, 240));
                } else if let Some(source) =
                    render::render_simple_click_fact_labeled(&fact.kernel, labels)
                {
                    detail.push_str("\n      fact + ");
                    detail.push_str(&trace_text(&source, 240));
                } else if step
                    .call_source
                    .as_ref()
                    .is_some_and(|call| !call.guarantees.is_empty())
                {
                    // The source guarantees already explain this call. A
                    // historical evaluated argument can prevent any exact
                    // caller-side Click proposition from naming its fact;
                    // do not turn the kernel rendering into a rival syntax.
                    unspelled += 1;
                    append_fact_snapshots(&fact.kernel, labels, &mut unspelled_snapshots);
                } else {
                    detail.push_str("\n      internal fact + (no exact Click spelling)");
                    detail.push_str("\n        kernel detail: ");
                    detail.push_str(&trace_text(
                        &render::render_proposition_labeled(&fact.kernel, labels),
                        240,
                    ));
                }
            }
            if unspelled > 0 {
                detail.push_str(&format!(
                    "\n      {unspelled} checked fact(s) have no exact caller-side Click spelling"
                ));
                if !unspelled_snapshots.is_empty() {
                    detail.push_str("; checked fact snapshot(s): ");
                    detail.push_str(&unspelled_snapshots.join(", "));
                }
            }
            if step.more_facts > 0 {
                detail.push_str(&format!("\n      … {} more facts", step.more_facts));
            }
            if let Some(frontier) = &step.frontier {
                detail.push_str("\n      C frontier: ");
                detail.push_str(frontier);
            }
            for (old, new, fact) in &step.resources {
                detail.push_str(&format!(
                    "\n      internal resource count {old} -> {new}: {}",
                    trace_text(&render::render_resource_fact_labeled(fact, labels), 240)
                ));
            }
            if step.more_resources > 0 {
                detail.push_str(&format!(
                    "\n      … {} more resource keys",
                    step.more_resources
                ));
            }
            if output.len() + detail.len() > MAX_RENDER_BYTES {
                output.push_str("\n    … <trace output limit reached>");
                break;
            }
            output.push_str(&detail);
            shown += 1;
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

/// The source template cannot express a historical evaluated argument, but
/// the checked fact can still identify its memory without printing a second
/// pseudo-language. Keep this diagnostic traversal independent of synthesis.
fn append_fact_snapshots(
    fact: &Proposition,
    labels: &mut SnapshotLabels,
    snapshots: &mut Vec<String>,
) {
    let mut pending = vec![fact];
    let mut visited = 0;
    while let Some(fact) = pending.pop() {
        visited += 1;
        if visited > 256 || snapshots.len() >= 32 {
            break;
        }
        let memories = match fact {
            Proposition::ConditionIs(condition, _) => {
                let mut memories = crate::kernel::c_condition_fact_memories(fact);
                let mut variables = std::collections::BTreeSet::new();
                crate::kernel::collect_condition_bitvector_variables(condition, &mut variables);
                for variable in variables {
                    if let Some((memory, _)) =
                        crate::kernel::registered_load_for_variable(&variable)
                    {
                        memories.push(memory.memory().clone());
                    }
                }
                memories
            }
            Proposition::CMemoryLoads { memory, .. }
            | Proposition::CMemoryCanStore { memory, .. }
            | Proposition::CMemoryLoadable { memory, .. } => vec![memory.clone()],
            Proposition::CMemoryMutatesOnly { before, after, .. }
            | Proposition::CMemoryEffectSummary { before, after, .. }
            | Proposition::CHeapAllocationFreed { before, after, .. } => {
                vec![before.clone(), after.clone()]
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
                Vec::new()
            }
            Proposition::Not(body)
            | Proposition::ForAll { body, .. }
            | Proposition::Exists { body, .. } => {
                pending.push(body);
                Vec::new()
            }
            _ => Vec::new(),
        };
        for memory in memories {
            let name = labels.snapshot_name(&memory);
            if !snapshots.contains(&name) {
                snapshots.push(name);
            }
        }
    }
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
            let trace = render("f", &[1], &mut labels).unwrap();
            assert!(goal.contains("snapshot#1"), "{goal}");
            assert!(
                trace.contains("kernel detail: viewable(memory=snapshot#1"),
                "{trace}"
            );
            assert!(
                trace.contains("kernel detail: viewable(memory=snapshot#2"),
                "{trace}"
            );
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
            register_scope(2, vec![1]);
            let trace = render("f", &[2, 3], &mut SnapshotLabels::default()).unwrap();
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
            let report = render("f", &[1], &mut SnapshotLabels::default()).unwrap();
            assert!(report.contains("fact + x == x"), "{report}");
            assert!(!report.contains("kernel detail"), "{report}");
        });
    }
}
