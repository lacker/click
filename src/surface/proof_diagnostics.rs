//! Structured context retained by proof-step failures.
//!
//! The semantic proof state is kept behind an opaque, shared provider.  This
//! keeps constructing an error cheap while allowing the terminal renderer to
//! inspect only the focused goal and bounded premise view when a human asks
//! for the error message.

use crate::kernel::Proposition;
use std::sync::Arc;

pub(crate) mod render;

/// A lazily inspectable proof state. Implementations retain a persistent proof
/// handle rather than cloning the goal, environment, or derivation history.
pub(crate) trait ProofDiagnosticState: Send + Sync {
    fn register_names(&self, _labels: &mut render::SnapshotLabels) {}
    fn source_goal(&self) -> Option<String> {
        None
    }
    fn kernel_goal(&self) -> Option<&Proposition>;
    fn premises(&self, limit: usize) -> Vec<&Proposition>;
    fn premise_count(&self) -> usize;
    fn proof_trace(&self, _claim: &str, _labels: &mut render::SnapshotLabels) -> Option<String> {
        None
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProofDiagnosticOrigin {
    pub stage: String,
    pub location: String,
}

#[derive(Clone)]
pub(crate) struct ProofFailureDiagnostic {
    pub origin: ProofDiagnosticOrigin,
    pub claim_label: String,
    pub reason: String,
    pub state: Option<Arc<dyn ProofDiagnosticState>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProofSearchFailure {
    pub strategy: String,
    pub reason: String,
    pub kind: String,
    pub diagnostic: Option<Arc<ProofFailureDiagnostic>>,
}

impl ProofFailureDiagnostic {
    pub(crate) fn kernel_goal(&self) -> Option<&Proposition> {
        self.state.as_ref()?.kernel_goal()
    }

    pub(crate) fn premises(&self, limit: usize) -> Vec<&Proposition> {
        self.state
            .as_ref()
            .map_or_else(Vec::new, |state| state.premises(limit))
    }

    pub(crate) fn premise_count(&self) -> usize {
        self.state.as_ref().map_or(0, |state| state.premise_count())
    }
}

impl std::fmt::Debug for ProofFailureDiagnostic {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ProofFailureDiagnostic")
            .field("origin", &self.origin)
            .field("claim_label", &self.claim_label)
            .field("reason", &self.reason)
            .finish_non_exhaustive()
    }
}

impl PartialEq for ProofFailureDiagnostic {
    fn eq(&self, other: &Self) -> bool {
        self.origin == other.origin
            && self.claim_label == other.claim_label
            && self.reason == other.reason
            && match (&self.state, &other.state) {
                (None, None) => true,
                (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                _ => false,
            }
    }
}

impl Eq for ProofFailureDiagnostic {}

pub(crate) fn render_terminal_message(
    summary: &str,
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
) -> String {
    render_terminal_message_labeled(
        summary,
        diagnostic,
        search_failures,
        &mut render::SnapshotLabels::default(),
    )
}

pub(crate) fn render_terminal_message_labeled(
    summary: &str,
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
    labels: &mut render::SnapshotLabels,
) -> String {
    if let Some(state) = &diagnostic.state {
        state.register_names(labels);
    }
    // Keep the established summary as the first line. The richer context is
    // deliberately bounded and rendered only at this terminal boundary.
    let mut rendered = summary.to_owned();
    rendered.push_str("\n  stage: ");
    rendered.push_str(&diagnostic.origin.stage);
    rendered.push_str("\n  location: ");
    rendered.push_str(&diagnostic.origin.location);
    // One label map for the whole report. Rendering the goal and each premise
    // with a map of its own made `snapshot#1` mean a different memory on every
    // line, so a premise that reads exactly like the goal could be about
    // another state entirely — which is the one thing a reader compares these
    // lines to decide.
    if let Some(goal) = diagnostic.kernel_goal() {
        if let Some(source) = diagnostic
            .state
            .as_ref()
            .and_then(|state| state.source_goal())
        {
            rendered.push_str("\n  goal: ");
            rendered.push_str(&source);
            if crate::surface::proof_trace::enabled_for(&diagnostic.claim_label) {
                let internal = render::render_proposition_labeled(goal, labels);
                if internal.contains("snapshot#") || internal.contains("snapshot<untracked>") {
                    rendered.push_str("\n  snapshot identity (internal): ");
                    rendered.push_str(&internal);
                }
            }
        } else if let Some(source) = render::render_simple_click_fact_labeled(goal, labels) {
            rendered.push_str("\n  goal: ");
            rendered.push_str(&source);
        } else {
            rendered.push_str("\n  internal goal (no exact Click spelling): ");
            rendered.push_str(&render::render_proposition_labeled(goal, labels));
        }
    }
    {
        let premises = diagnostic.premises(8);
        if !premises.is_empty() {
            let total = diagnostic.premise_count();
            rendered.push_str(&format!(
                "\n  recent premises (showing {} of {total}):",
                premises.len()
            ));
            for premise in &premises {
                rendered.push_str("\n    ");
                let text = render::render_simple_click_fact_labeled(premise, labels)
                    .unwrap_or_else(|| {
                        format!(
                            "internal (no exact Click spelling): {}",
                            render::render_proposition_labeled(premise, labels)
                        )
                    });
                let mut end = text.len().min(2048);
                while end > 0 && !text.is_char_boundary(end) {
                    end -= 1;
                }
                rendered.push_str(&text[..end]);
                if end < text.len() {
                    rendered.push('…');
                }
            }
        }
        if diagnostic.premise_count() > premises.len() {
            rendered.push_str("\n    … <additional premises omitted>");
        }
    }
    if !search_failures.is_empty() {
        rendered.push_str("\n  search candidates:");
        for failure in search_failures.iter().take(8) {
            rendered.push_str("\n    ");
            rendered.push_str(&failure.strategy);
            rendered.push_str(" [");
            rendered.push_str(&failure.kind);
            rendered.push_str("]: ");
            rendered.push_str(&failure.reason);
            if failure.kind == "UnclosedGoal"
                && let Some(goal) = failure
                    .diagnostic
                    .as_ref()
                    .and_then(|diagnostic| diagnostic.kernel_goal())
            {
                rendered.push_str("; internal goal: ");
                rendered.push_str(&render::render_proposition_labeled(goal, labels));
            }
        }
        if search_failures.len() > 8 {
            rendered.push_str("\n    … <additional search candidates omitted>");
        }
    }
    const MAX_REPORT_BYTES: usize = 64 * 1024;
    if rendered.len() > MAX_REPORT_BYTES {
        let mut end = MAX_REPORT_BYTES.saturating_sub("\n… <proof diagnostic truncated>".len());
        while end > 0 && !rendered.is_char_boundary(end) {
            end -= 1;
        }
        rendered.truncate(end);
        rendered.push_str("\n… <proof diagnostic truncated>");
    }
    rendered
}

pub(crate) fn render_search_failures(summary: &str, failures: &[ProofSearchFailure]) -> String {
    let mut rendered = summary.to_owned();
    rendered.push_str("\n  search candidates:");
    for failure in failures.iter().take(8) {
        rendered.push_str("\n    ");
        rendered.push_str(&failure.strategy);
        rendered.push_str(" [");
        rendered.push_str(&failure.kind);
        rendered.push_str("]: ");
        rendered.push_str(&failure.reason);
        if let Some(goal) = failure
            .diagnostic
            .as_ref()
            .and_then(|diagnostic| diagnostic.kernel_goal())
        {
            rendered.push_str("; goal: ");
            rendered.push_str(&render::render_proposition(goal));
        }
    }
    if failures.len() > 8 {
        rendered.push_str("\n    … <additional search candidates omitted>");
    }
    const MAX_REPORT_BYTES: usize = 64 * 1024;
    if rendered.len() > MAX_REPORT_BYTES {
        let mut end = MAX_REPORT_BYTES.saturating_sub("\n… <proof diagnostic truncated>".len());
        while end > 0 && !rendered.is_char_boundary(end) {
            end -= 1;
        }
        rendered.truncate(end);
        rendered.push_str("\n… <proof diagnostic truncated>");
    }
    rendered
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct CountingState {
        goal: Proposition,
        calls: AtomicUsize,
    }

    impl ProofDiagnosticState for CountingState {
        fn kernel_goal(&self) -> Option<&Proposition> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            Some(&self.goal)
        }
        fn premises(&self, limit: usize) -> Vec<&Proposition> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            vec![&self.goal][..limit.min(1)].to_vec()
        }
        fn premise_count(&self) -> usize {
            3
        }
    }

    #[test]
    fn rendering_is_the_boundary_that_visits_retained_context() {
        let state = Arc::new(CountingState {
            goal: Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true),
            calls: AtomicUsize::new(0),
        });
        let diagnostic = ProofFailureDiagnostic {
            origin: ProofDiagnosticOrigin {
                stage: "proof step".into(),
                location: "source tactic 4".into(),
            },
            claim_label: "claim".into(),
            reason: "reason".into(),
            state: Some(state.clone()),
        };
        assert_eq!(state.calls.load(Ordering::Relaxed), 0);
        let report = render_terminal_message("reason", &diagnostic, &[]);
        assert!(report.contains("stage: proof step"));
        assert!(report.contains("additional premises omitted"));
        assert!(state.calls.load(Ordering::Relaxed) >= 2);
    }

    #[test]
    fn click_error_lazily_caches_and_preserves_structured_context() {
        let state = Arc::new(CountingState {
            goal: Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true),
            calls: AtomicUsize::new(0),
        });
        let diagnostic = ProofFailureDiagnostic {
            origin: ProofDiagnosticOrigin {
                stage: "step".into(),
                location: "source tactic 44".into(),
            },
            claim_label: "claim".into(),
            reason: "failed".into(),
            state: Some(state.clone()),
        };
        let error = crate::surface::ClickError::with_diagnostic("failed", diagnostic);
        assert_eq!(state.calls.load(Ordering::Relaxed), 0);
        let first = error.message().to_owned();
        let after_first = state.calls.load(Ordering::Relaxed);
        assert_eq!(first, error.message());
        assert_eq!(after_first, state.calls.load(Ordering::Relaxed));
        let wrapped = error.clone().with_context("outer");
        assert!(wrapped.diagnostic().is_some());
        assert!(wrapped.message().contains("outer"));
    }

    #[test]
    fn reported_trace_uses_the_goals_snapshot_labels() {
        use crate::kernel::{Bitvector32Term, CMemory, Pointer, PointerBlock, PointerOffsetTerm};

        struct TracedState(Proposition);
        impl ProofDiagnosticState for TracedState {
            fn kernel_goal(&self) -> Option<&Proposition> {
                Some(&self.0)
            }
            fn premises(&self, _limit: usize) -> Vec<&Proposition> {
                Vec::new()
            }
            fn premise_count(&self) -> usize {
                0
            }
            fn proof_trace(
                &self,
                claim: &str,
                labels: &mut render::SnapshotLabels,
            ) -> Option<String> {
                crate::surface::proof_trace::render(claim, &[1], labels)
            }
        }
        let at = |memory| Proposition::CMemoryLoadable {
            memory,
            base: Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(1),
        };
        crate::surface::with_proof_trace("f", || {
            let memory = CMemory::new().with_block("shared", 1);
            crate::surface::proof_trace::record(
                1,
                crate::surface::proof_trace::TraceStep {
                    header: "\n    source tactic 0: step".into(),
                    call_source: None,
                    facts: vec![crate::surface::proof_trace::TraceFact {
                        kernel: at(memory.clone()),
                        source: None,
                    }],
                    more_facts: 0,
                    frontier: None,
                    resources: Vec::new(),
                    more_resources: 0,
                },
            );
            let diagnostic = ProofFailureDiagnostic {
                origin: ProofDiagnosticOrigin {
                    stage: "proof step".into(),
                    location: "source tactic 1".into(),
                },
                claim_label: "f.contract".into(),
                reason: "failed".into(),
                state: Some(Arc::new(TracedState(at(memory)))),
            };
            let report = crate::surface::ClickError::with_diagnostic("failed", diagnostic).report();
            assert!(
                report.contains(
                    "internal goal (no exact Click spelling): viewable(memory=snapshot#1"
                ),
                "{report}"
            );
            assert!(
                report.contains("kernel detail: viewable(memory=snapshot#1"),
                "{report}"
            );
        });
    }

    #[test]
    fn search_only_reports_are_utf8_safe_and_bounded() {
        let failures = (0..32)
            .map(|index| ProofSearchFailure {
                strategy: format!("策略 {index}"),
                reason: "失敗🙂".repeat(20_000),
                kind: "rejected".into(),
                diagnostic: None,
            })
            .collect::<Vec<_>>();
        let report = render_search_failures("failed", &failures);
        assert!(report.len() <= 64 * 1024);
        assert!(report.contains("proof diagnostic truncated"));
        assert!(report.is_char_boundary(report.len()));
    }

    #[test]
    fn terminal_search_report_renders_unclosed_goal_lazily() {
        let state = Arc::new(CountingState {
            goal: Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true),
            calls: AtomicUsize::new(0),
        });
        let diagnostic = Arc::new(ProofFailureDiagnostic {
            origin: ProofDiagnosticOrigin {
                stage: "proof step".into(),
                location: "loop closure".into(),
            },
            claim_label: "claim".into(),
            reason: "leaf remained open".into(),
            state: Some(state),
        });
        let report = render_terminal_message(
            "closure failed",
            &ProofFailureDiagnostic {
                origin: ProofDiagnosticOrigin {
                    stage: "proof step".into(),
                    location: "loop closure".into(),
                },
                claim_label: "claim".into(),
                reason: "closure failed".into(),
                state: None,
            },
            &[ProofSearchFailure {
                strategy: "loop invariant bundle leaf".into(),
                reason: "leaf remained open".into(),
                kind: "UnclosedGoal".into(),
                diagnostic: Some(diagnostic),
            }],
        );
        assert!(report.contains("[UnclosedGoal]"));
        assert!(report.contains("goal: true"));
    }
}
