use super::*;

pub(super) struct TacticTiming {
    pub(super) claim_label: String,
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) tactic_name: String,
    pub(super) tactic_class: &'static str,
    pub(super) statement_index: usize,
    pub(super) start: std::time::Instant,
    pub(super) context: TimingTacticContext,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::lang::click) enum SourceTacticClass {
    Simple,
    Smart,
    Control,
    Internal,
}

impl SourceTacticClass {
    fn label(self) -> &'static str {
        match self {
            Self::Simple => "simple",
            Self::Smart => "smart",
            Self::Control => "control",
            Self::Internal => "internal",
        }
    }
}

pub(in crate::lang::click) fn source_tactic_class(tactic: &ProofTactic) -> SourceTacticClass {
    if let ProofTactic::Have(have) = tactic {
        if smart_simp_unfold_prefix(&have.proof).is_some() {
            return SourceTacticClass::Smart;
        }
        if let Proof::Script(tactics) = &have.proof
            && !tactics.is_empty()
            && tactics
                .iter()
                .all(|tactic| matches!(tactic.class(), TacticClass::Simple(_)))
        {
            return SourceTacticClass::Simple;
        }
    }
    if let ProofTactic::Loop(loop_clause) = tactic
        && (loop_clause.initialize_proof().is_none()
            || loop_clause.preserve_proof().is_none()
            || loop_clause
                .items()
                .iter()
                .any(|item| item.is_effect_kind() && matches!(item.proof(), Proof::Default)))
    {
        // The loop keyword is the shared source anchor for every omitted
        // phase/effect proof in this block. Expanding it materializes all of
        // those defaults together.
        return SourceTacticClass::Smart;
    }
    match tactic.class() {
        TacticClass::Simple(_) => SourceTacticClass::Simple,
        TacticClass::Smart(_) => SourceTacticClass::Smart,
        TacticClass::ControlFlow(_) => SourceTacticClass::Control,
        TacticClass::Internal(_) => SourceTacticClass::Internal,
    }
}

pub(super) fn has_independent_source_timing(tactic: &ProofTactic) -> bool {
    // `CertifiedAlternatives` is the internal branching plan produced by a
    // smart `execute`. It has no surface spelling or source site of its own:
    // replaying and lowering it is part of the owning smart tactic. Starting
    // a nested control timer here would hide the expensive part of `execute`
    // from `click profile` and subject `click expand` to the control budget.
    !matches!(tactic.class(), TacticClass::Internal(_))
        && !matches!(tactic, ProofTactic::CertifiedAlternatives(_))
}

impl TacticTiming {
    pub(super) fn new(
        claim_label: &str,
        tactic_index: usize,
        source_index: usize,
        tactic: &ProofTactic,
        statement_index: usize,
    ) -> Option<Self> {
        if !has_independent_source_timing(tactic) {
            return None;
        }
        Self::named_for_tactic(
            claim_label,
            tactic_name(tactic),
            tactic,
            tactic_index,
            source_index,
            statement_index,
        )
    }

    /// Times work that is not itself a surface tactic replay — a planner
    /// searching for a certificate, or a kernel re-derivation that a replayed
    /// tactic defers to its caller — under an explicit `name`, taking the
    /// class from the tactic the work belongs to rather than inventing one.
    pub(super) fn named_for_tactic(
        claim_label: &str,
        name: &str,
        tactic: &ProofTactic,
        tactic_index: usize,
        source_index: usize,
        statement_index: usize,
    ) -> Option<Self> {
        if source_index == usize::MAX || matches!(tactic.class(), TacticClass::Internal(_)) {
            return None;
        }
        crate::instrumentation::enabled().then(|| {
            let tactic_class = source_tactic_class(tactic).label();
            if crate::instrumentation::starts_enabled() {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(
                        crate::instrumentation::TacticEvent {
                            claim: claim_label.to_string(),
                            tactic_index,
                            tactic_name: name.to_string(),
                            class: tactic_class.to_string(),
                            statement_index,
                            source_index,
                        },
                    ),
                );
            }
            let context = TimingTacticContext {
                claim_label: claim_label.to_string(),
                tactic_index,
                tactic_name: name.to_string(),
                tactic_class: tactic_class.to_string(),
                statement_index,
                source_index,
            };
            push_timing_tactic(context.clone());
            Self {
                claim_label: claim_label.to_string(),
                tactic_index,
                source_index,
                tactic_name: name.to_string(),
                tactic_class,
                statement_index,
                start: std::time::Instant::now(),
                context,
            }
        })
    }
}

impl Drop for TacticTiming {
    fn drop(&mut self) {
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticFinished {
            tactic: crate::instrumentation::TacticEvent {
                claim: self.claim_label.clone(),
                tactic_index: self.tactic_index,
                tactic_name: self.tactic_name.clone(),
                class: self.tactic_class.to_string(),
                statement_index: self.statement_index,
                source_index: self.source_index,
            },
            elapsed: self.start.elapsed(),
            work: 0,
        });
        pop_timing_tactic(&self.context);
    }
}
