//! Structured context retained by proof-step failures.
//!
//! The semantic proof state is kept behind an opaque, shared provider.  This
//! keeps constructing an error cheap while allowing the terminal renderer to
//! inspect only the focused goal and bounded premise view when a human asks
//! for the error message.

use crate::kernel::Proposition;
use std::sync::Arc;

pub(crate) mod render;

pub(crate) const MAX_SEARCH_REASON_BYTES: usize = 512;

pub(crate) fn truncate_search_reason(reason: &mut String) {
    if reason.len() > MAX_SEARCH_REASON_BYTES {
        let mut end = MAX_SEARCH_REASON_BYTES;
        while !reason.is_char_boundary(end) {
            end -= 1;
        }
        reason.truncate(end);
    }
}

/// Keep selected facts unformatted until the terminal proof state supplies
/// its local and recorded-state names. Capture at most four facts, and
/// retain only shared entry naming for reports without a proof state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProofSearchPremiseExcerpt {
    premises: Vec<Proposition>,
    remaining: usize,
    naming: render::CapturedNaming,
}

impl ProofSearchPremiseExcerpt {
    pub(crate) fn new(premises: &[&Proposition]) -> Self {
        const LIMIT: usize = 4;
        Self {
            premises: premises
                .iter()
                .take(LIMIT)
                .map(|fact| (**fact).clone())
                .collect(),
            remaining: premises.len().saturating_sub(LIMIT),
            naming: render::CapturedNaming::capture(),
        }
    }
}

/// The history result retained while the failing proof's verification session
/// is active. Formatting must not rerun the walk under a different session or
/// bridging mode, nor recover the write width from a later arena.
#[derive(Clone)]
pub(crate) struct MemoryHistoryDiagnostic {
    pub explanation: crate::kernel::resource_tracker::Explanation,
    pub written_bytes: Option<u32>,
    /// The statement whose store the walk stopped at, and the fact the
    /// implicit tail's store search spelled and could not prove before it,
    /// when the failing path recorded that miss for this cell.
    pub store_search_miss: Option<StoreSearchMiss>,
}

/// A store-search miss as a report prints it: the statement as a proof
/// names it, and the search's own spelling of the index disequality.
#[derive(Clone)]
pub(crate) struct StoreSearchMiss {
    pub statement: String,
    /// The dropped cell as the statement's C locals spelled it.
    pub cell: Option<String>,
    pub fact: String,
}

impl MemoryHistoryDiagnostic {
    pub(crate) fn capture(explanation: crate::kernel::resource_tracker::Explanation) -> Self {
        let written_bytes = explanation
            .outcome
            .blocking_step()
            .and_then(|(at, _)| at)
            .and_then(|at| at.shared_memory().derivation())
            .and_then(|derivation| match derivation.as_ref() {
                crate::kernel::MemoryDerivation::Store { value, .. } => {
                    Some(value.program_type().byte_width())
                }
                _ => None,
            });
        Self {
            explanation,
            written_bytes,
            store_search_miss: None,
        }
    }
}

/// A lazily inspectable proof state. Implementations retain a persistent proof
/// handle rather than cloning the goal, environment, or derivation history.
pub(crate) trait ProofDiagnosticState: Send + Sync {
    fn register_names(&self, _labels: &mut render::MemoryStateLabels) {}

    fn failed_requirement(&self) -> Option<(&str, &Proposition)> {
        None
    }

    fn rejected_resource_fact(&self) -> Option<&crate::kernel::proof::RejectedResourceRewriteFact> {
        None
    }

    /// The instance a refused `fold` proposed, when its resource declares no
    /// field and keeps its children's fields in a hidden record.
    fn proposed_hidden_record(&self) -> Option<&crate::kernel::ResourceInstance> {
        None
    }

    fn memory_history(&self) -> Option<&MemoryHistoryDiagnostic> {
        None
    }

    fn read_resolutions(&self) -> &[crate::kernel::ReadResolutionDiagnostic] {
        &[]
    }

    fn proof_context_kind(&self) -> Option<&str> {
        None
    }

    fn resources(&self) -> &[crate::kernel::ResourceFact] {
        &[]
    }

    fn kernel_goal(&self) -> Option<&Proposition>;

    /// The source form of the focused proposition, when the proof retained it.
    fn authored_goal(&self) -> Option<&super::ClickProposition> {
        None
    }

    /// The retained written goal when the source spelling carries pointer
    /// information that an address rendering could lose.
    fn written_pointer_goal(&self) -> Option<&super::ClickProposition> {
        None
    }

    fn premises(&self, limit: usize) -> Vec<&Proposition>;
    fn premise_count(&self) -> usize;
    fn proof_trace(
        &self,
        _claim: &str,
        _labels: &mut render::MemoryStateLabels,
        _tactic_location: &dyn Fn(&[usize]) -> Option<(String, crate::source::SourcePosition)>,
        _branch_arm: &dyn Fn(&[usize], &crate::source::SourcePosition) -> Option<usize>,
        _have_body_contains: &dyn Fn(&[usize], &crate::source::SourcePosition) -> bool,
        _target: Option<&crate::source::SourcePosition>,
        _failing_path: Option<usize>,
    ) -> Option<String> {
        None
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProofDiagnosticStage {
    CheckedStep,
    KnownGoalUnavailable,
    Other(&'static str),
}

impl ProofDiagnosticStage {
    fn label(self) -> &'static str {
        match self {
            Self::CheckedStep | Self::KnownGoalUnavailable => "proof step",
            Self::Other(label) => label,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProofDiagnosticOrigin {
    pub stage: ProofDiagnosticStage,
    pub location: String,
    /// Written outer tactic and each nested `have`/`with` body position.
    pub source_tactic_path: Option<Vec<usize>>,
}

#[derive(Clone)]
pub(crate) struct ProofFailureDiagnostic {
    pub origin: ProofDiagnosticOrigin,
    pub claim_label: String,
    pub reason: String,
    pub checks: Option<Arc<CheckObservations>>,
    pub state: Option<Arc<dyn ProofDiagnosticState>>,
    /// The function outcome path the failure lies on, when it names one.
    /// The trace shows the arm of a terminal join that holds it.
    pub failing_path: Option<usize>,
}

/// Bounded observations of queries actually executed by one written check.
/// They are diagnostic records, including speculative search, never premises.
#[derive(Clone)]
pub(crate) struct CheckObservations {
    pub reads: Vec<crate::kernel::ReadResolutionDiagnostic>,
    pub walks: Vec<crate::kernel::TransportCellWalkDiagnostic>,
}

pub(crate) fn capture_check_observations<T>(run: impl FnOnce() -> T) -> (T, CheckObservations) {
    crate::kernel::with_bounded_cell_walk_diagnostics(|| {
        let (result, reads) = crate::kernel::capture_read_resolutions(run);
        let walks = crate::kernel::take_transport_cell_walk_diagnostics();
        (result, CheckObservations { reads, walks })
    })
}

pub(crate) fn render_check_observations(
    checks: &CheckObservations,
    labels: &mut render::MemoryStateLabels,
    traced: bool,
) -> String {
    let limit = if traced { 16 } else { 2 };
    let mut result =
        String::from("checks observed during the failed attempt (queries, not established facts):");
    for read in checks.reads.iter().take(limit) {
        result.push_str("\n  ");
        if traced {
            result.push_str(&render::render_read_resolution(read, labels));
        } else {
            result.push_str(&format!(
                "read-value check: {}; recovered value {}; comparison {}",
                read.reason,
                if read.recovered.is_some() {
                    "available"
                } else {
                    "not recovered"
                },
                if read.equal { "proved" } else { "not proved" }
            ));
        }
    }
    for walk in checks.walks.iter().take(limit) {
        result.push_str("\n  cell walk: ");
        if traced {
            result.push_str(&render::render_transport_cell_walk(walk, labels));
        } else {
            result.push_str(&format!(
                "{}-byte read; {}; from {} to {}",
                walk.bytes,
                walk.reason,
                labels.state_phrase(walk.start.memory()),
                labels.state_phrase(walk.stopped_at.memory())
            ));
        }
    }
    if checks.reads.is_empty() && checks.walks.is_empty() {
        result.push_str("\n  no instrumented memory query was recorded; the failure may precede a cell walk or use another rule");
    }
    if checks.reads.len() > limit || checks.walks.len() > limit {
        result.push_str("\n  … additional observations omitted");
    }
    if checks.reads.len() >= 16 || checks.walks.len() >= 16 {
        result.push_str("\n  capture limited to 16 distinct cell walks and 16 read queries");
    }
    result
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProofSearchFailure {
    pub strategy: String,
    pub reason: String,
    pub kind: String,
    pub diagnostic: Option<Arc<ProofFailureDiagnostic>>,
    pub premise_excerpt: Option<ProofSearchPremiseExcerpt>,
}

fn render_search_reason(
    failure: &ProofSearchFailure,
    labels: &mut render::MemoryStateLabels,
) -> String {
    let Some(excerpt) = &failure.premise_excerpt else {
        return failure.reason.clone();
    };
    excerpt.naming.register_if_missing(labels);
    let mut reason = failure.reason.clone();
    for (index, premise) in excerpt.premises.iter().enumerate() {
        if reason.len() >= MAX_SEARCH_REASON_BYTES {
            break;
        }
        if index != 0 {
            reason.push_str("; ");
        }
        reason.push_str(&render::render_proposition_labeled(premise, labels));
    }
    if excerpt.remaining != 0 && reason.len() < MAX_SEARCH_REASON_BYTES {
        reason.push_str(&format!("; … {} more", excerpt.remaining));
    }
    truncate_search_reason(&mut reason);
    reason
}

impl ProofFailureDiagnostic {
    pub(crate) fn kernel_goal(&self) -> Option<&Proposition> {
        self.state.as_ref()?.kernel_goal()
    }

    pub(in crate::surface) fn render_goal(
        &self,
        labels: &mut render::MemoryStateLabels,
    ) -> Option<String> {
        let state = self.state.as_ref()?;
        if let Some(goal) = state.written_pointer_goal() {
            return Some(super::printing::source_click_proposition(goal));
        }
        Some(render::render_proposition_labeled(
            state.kernel_goal()?,
            labels,
        ))
    }

    pub(in crate::surface) fn known_goal_refusal(
        &self,
        labels: &mut render::MemoryStateLabels,
    ) -> Option<String> {
        if self.origin.stage != ProofDiagnosticStage::KnownGoalUnavailable {
            return None;
        }
        let state = self.state.as_ref()?;
        state.register_names(labels);
        let goal = if let Some(authored) = state.authored_goal() {
            super::printing::source_click_proposition(authored)
        } else {
            self.render_goal(labels)?
        };
        Some(format!(
            "You must prove `{goal}` in order to use the tactic `known()`."
        ))
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
            && self.failing_path == other.failing_path
            && match (&self.checks, &other.checks) {
                (None, None) => true,
                (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                _ => false,
            }
            && match (&self.state, &other.state) {
                (None, None) => true,
                (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                _ => false,
            }
    }
}

impl Eq for ProofFailureDiagnostic {}

/// Whether `premise` is kernel authority that no Click proof can cite
/// ([`Proposition::is_kernel_authority`]).
pub(crate) fn is_internal_premise(premise: &Proposition) -> bool {
    premise.is_kernel_authority()
}

/// The premises a reader can use, and how many internal ones were set aside.
pub(crate) fn without_internal_premises(premises: Vec<&Proposition>) -> (Vec<&Proposition>, usize) {
    let total = premises.len();
    let kept = premises
        .into_iter()
        .filter(|premise| !is_internal_premise(premise))
        .collect::<Vec<_>>();
    let internal = total - kept.len();
    (kept, internal)
}

/// Requirements use exactly the same proposition policy as facts and goals.
/// Whether the failed step's requirement is its goal, printed as `goal:`.
pub(crate) fn requirement_is_goal(state: &dyn ProofDiagnosticState) -> bool {
    state
        .failed_requirement()
        .is_some_and(|(label, _)| label == "goal")
}

pub(crate) fn render_failed_requirement(
    state: &dyn ProofDiagnosticState,
    labels: &mut render::MemoryStateLabels,
) -> String {
    state.register_names(labels);
    let mut result = String::new();
    if let Some((label, proposition)) = state.failed_requirement() {
        result = format!(
            "{label}: {}",
            render::render_proposition_labeled(proposition, labels)
        );
        // The body fact of a resource without fields reads its hidden
        // record; show the record the fold proposed, in the same labels.
        if let Some(instance) = state.proposed_hidden_record()
            && let Some(record) = render::render_hidden_record_instance_labeled(
                instance.name(),
                &(instance.arguments()).native_values(),
                instance.schema().fields(),
                &instance.fields().native_values(),
                labels,
            )
        {
            result.push_str("\nproposed fold: ");
            result.push_str(&record);
        }
    }
    if let Some(refusal) = state.rejected_resource_fact() {
        if !result.is_empty() {
            result.push('\n');
        }
        result.push_str("rejected fact: ");
        result.push_str(&render::render_proposition_labeled(
            &refusal.rejected,
            labels,
        ));
        result.push_str("\nallowed facts from the checked resource body:");
        if refusal.allowed.is_empty() {
            result.push_str(" none");
        }
        for fact in refusal.allowed.iter().take(12) {
            result.push_str("\n  ");
            result.push_str(&render::render_proposition_labeled(fact, labels));
        }
        if refusal.allowed.len() > 12 {
            let count = refusal.allowed.len() - 12;
            let noun = if count == 1 { "fact" } else { "facts" };
            result.push_str(&format!("\n  … {count} more allowed {noun}"));
        }
    }
    result
}

pub(crate) fn render_terminal_message(
    summary: &str,
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
) -> String {
    render_terminal_message_labeled(
        summary,
        diagnostic,
        search_failures,
        &mut render::MemoryStateLabels::ambient(),
    )
}

pub(crate) fn render_terminal_message_labeled(
    summary: &str,
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
    labels: &mut render::MemoryStateLabels,
) -> String {
    render_diagnostic_labeled(
        Some(summary),
        diagnostic,
        search_failures,
        RequiredGoal::default(),
        labels,
    )
}

#[cfg(test)]
pub(crate) fn render_trace_context_labeled(
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
    labels: &mut render::MemoryStateLabels,
) -> String {
    render_trace_context_with_requirement(diagnostic, search_failures, None, None, labels)
}

/// [`render_trace_context_labeled`] for a failure whose open goal is the
/// `requirement` or `resource` a refused C operation needed, when the proof
/// state holds no focused proposition goal.
pub(crate) fn render_trace_context_with_requirement(
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
    requirement: Option<&Proposition>,
    resource: Option<&crate::kernel::ResourceFact>,
    labels: &mut render::MemoryStateLabels,
) -> String {
    let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
    // Only explicit trace rendering pays for collision detection. The first
    // bounded rendering collects exactly the footprints displayed below; a
    // collision triggers one rerender so both earlier and later occurrences
    // receive the same report-local labels. No proof operation is rerun.
    labels.begin_range_collision_detection();
    let required = RequiredGoal {
        requirement,
        resource,
    };
    let first = render_diagnostic_labeled(None, diagnostic, search_failures, required, labels);
    let report = if labels.finish_range_collision_detection() {
        render_diagnostic_labeled(None, diagnostic, search_failures, required, labels)
    } else {
        first
    };
    labels.end_range_collision_detection();
    report
}

/// What a refused C operation needed, when it is the report's goal.
#[derive(Clone, Copy, Default)]
struct RequiredGoal<'a> {
    requirement: Option<&'a Proposition>,
    resource: Option<&'a crate::kernel::ResourceFact>,
}

fn render_diagnostic_labeled(
    summary: Option<&str>,
    diagnostic: &ProofFailureDiagnostic,
    search_failures: &[ProofSearchFailure],
    required: RequiredGoal<'_>,
    labels: &mut render::MemoryStateLabels,
) -> String {
    if let Some(state) = &diagnostic.state {
        state.register_names(labels);
    }
    // Keep the established summary as the first line. The richer context is
    // deliberately bounded and rendered only at this terminal boundary.
    let mut rendered = summary.unwrap_or_default().to_owned();
    let known_refusal = summary
        .is_none()
        .then(|| diagnostic.known_goal_refusal(labels))
        .flatten();
    if summary.is_none() {
        rendered.push_str("proof refusal:\n  ");
        rendered.push_str(known_refusal.as_deref().unwrap_or(&diagnostic.reason));
        rendered.push_str("\n  stage: ");
        rendered.push_str(diagnostic.origin.stage.label());
        rendered.push_str("\n  location: ");
        rendered.push_str(&diagnostic.origin.location);
    }
    if summary.is_none()
        && let Some(kind) = diagnostic
            .state
            .as_ref()
            .and_then(|state| state.proof_context_kind())
    {
        rendered.push_str("\n  proof context: ");
        rendered.push_str(kind);
    }
    if summary.is_none()
        && let Some(state) = &diagnostic.state
    {
        let resources = state.resources();
        rendered.push_str(&format!(
            "\n  resources in scope (showing {} of {}):",
            resources.len().min(12),
            resources.len()
        ));
        for fact in resources.iter().take(12) {
            rendered.push_str("\n    ");
            rendered.push_str(&render::render_resource_fact_labeled(fact, labels));
        }
        if resources.len() > 12 {
            rendered.push_str("\n    … additional resources omitted");
        }
    }
    if summary.is_some() {
        rendered.push_str("\n  stage: ");
        rendered.push_str(diagnostic.origin.stage.label());
        rendered.push_str("\n  location: ");
        rendered.push_str(&diagnostic.origin.location);
    }
    // One label map for the whole report. Rendering the goal and each premise
    // with a map of its own made `state#1` mean a different memory on every
    // line, so a premise that reads exactly like the goal could be about
    // another state entirely — which is the one thing a reader compares these
    // lines to decide.
    if let Some(state) = &diagnostic.state {
        let requirement = render_failed_requirement(state.as_ref(), labels);
        if !requirement.is_empty() {
            rendered.push_str("\n  ");
            rendered.push_str(&requirement);
        }
    }
    // A refused step that names its own goal (a fold's body fact) printed it
    // above; the enclosing branch's goal would be a second `goal:` line.
    let requirement_is_goal = diagnostic
        .state
        .as_ref()
        .is_some_and(|state| requirement_is_goal(state.as_ref()));
    if requirement_is_goal || known_refusal.is_some() {
        // The requirement or the refusal already identified this goal.
    } else if let Some(goal) = diagnostic.render_goal(labels) {
        rendered.push_str("\n  goal: ");
        rendered.push_str(&goal);
        if let Some(history) = diagnostic
            .state
            .as_ref()
            .and_then(|state| state.memory_history())
            && let Some(history) = render::render_memory_history_check(history, labels)
        {
            rendered.push_str("\n  ");
            rendered.push_str(&history);
        }
    } else if let Some(goal) = required.requirement {
        // A refused execution step's goal is the requirement it could not
        // establish at the statement's pre-state.
        rendered.push_str("\n  goal: ");
        rendered.push_str(&render::render_proposition_labeled(goal, labels));
    } else if let Some(resource) = required.resource {
        rendered.push_str("\n  goal: ");
        rendered.push_str(&render::render_resource_fact_spelled(resource, labels));
    }
    if let Some(state) = &diagnostic.state {
        for resolution in state.read_resolutions() {
            rendered.push_str("\n  ");
            rendered.push_str(&render::render_read_resolution(resolution, labels));
        }
    }
    let recent = diagnostic.premises(if summary.is_some() { 8 } else { 16 });
    let (premises, internal) = without_internal_premises(recent);
    if !premises.is_empty() || internal != 0 {
        let heading = if summary.is_some() {
            "recent premises"
        } else {
            "premises in scope"
        };
        rendered.push_str(&format!(
            "\n  {heading} (showing {} of {}):",
            premises.len(),
            diagnostic.premise_count()
        ));
        for premise in &premises {
            rendered.push_str("\n    ");
            rendered.push_str(&render::render_proposition_labeled(premise, labels));
        }
        if internal != 0 {
            rendered.push_str(&format!(
                "\n    … <{internal} internal bookkeeping {} not shown>",
                if internal == 1 { "fact" } else { "facts" }
            ));
        }
    }
    if diagnostic.premise_count() > premises.len() + internal {
        rendered.push_str("\n    … <additional premises omitted>");
    }
    if let Some(checks) = &diagnostic.checks
        && (summary.is_none() || !checks.reads.is_empty() || !checks.walks.is_empty())
    {
        rendered.push_str("\n  ");
        rendered.push_str(&render_check_observations(
            checks,
            labels,
            summary.is_none(),
        ));
    }
    if !search_failures.is_empty() {
        rendered.push_str("\n  search candidates:");
        for failure in search_failures.iter().take(8) {
            rendered.push_str("\n    ");
            rendered.push_str(&failure.strategy);
            rendered.push_str(" [");
            rendered.push_str(&failure.kind);
            rendered.push_str("]: ");
            rendered.push_str(&render_search_reason(failure, labels));
            if let Some(state) = failure
                .diagnostic
                .as_ref()
                .and_then(|diagnostic| diagnostic.state.as_ref())
            {
                let requirement = render_failed_requirement(state.as_ref(), labels);
                if !requirement.is_empty() {
                    rendered.push_str("; ");
                    rendered.push_str(&requirement);
                }
            }
            if failure.kind == "UnclosedGoal"
                && let Some(goal) = failure
                    .diagnostic
                    .as_ref()
                    .and_then(|diagnostic| diagnostic.kernel_goal())
            {
                rendered.push_str("; goal: ");
                rendered.push_str(&render::render_proposition_labeled(goal, labels));
            }
        }
        if search_failures.len() > 8 {
            rendered.push_str("\n    … <additional search candidates omitted>");
        }
    }
    if summary.is_some() && !crate::surface::proof_trace::enabled_for(&diagnostic.claim_label) {
        rendered.push_str(&labels.trace_legend());
    }
    if summary.is_none() {
        rendered.push_str(&labels.range_collision_legend());
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
    if summary.is_none() {
        // The trace is a separate section after the ordinary CLI error. Keep
        // its nested hierarchy, but remove the old report-wide indentation.
        rendered = rendered
            .trim_start_matches('\n')
            .lines()
            .map(|line| line.strip_prefix("  ").unwrap_or(line))
            .collect::<Vec<_>>()
            .join("\n");
    }
    rendered
}

pub(crate) fn render_search_failures(summary: &str, failures: &[ProofSearchFailure]) -> String {
    let mut labels = render::MemoryStateLabels::default();
    if let Some(state) = failures
        .iter()
        .find_map(|failure| failure.diagnostic.as_ref()?.state.as_ref())
    {
        state.register_names(&mut labels);
    }
    let mut rendered = summary.to_owned();
    rendered.push_str("\n  search candidates:");
    for failure in failures.iter().take(8) {
        rendered.push_str("\n    ");
        rendered.push_str(&failure.strategy);
        rendered.push_str(" [");
        rendered.push_str(&failure.kind);
        rendered.push_str("]: ");
        rendered.push_str(&render_search_reason(failure, &mut labels));
        if let Some(state) = failure
            .diagnostic
            .as_ref()
            .and_then(|diagnostic| diagnostic.state.as_ref())
        {
            let requirement = render_failed_requirement(state.as_ref(), &mut labels);
            if !requirement.is_empty() {
                rendered.push_str("; ");
                rendered.push_str(&requirement);
            }
        }

        if let Some(goal) = failure
            .diagnostic
            .as_ref()
            .and_then(|diagnostic| diagnostic.render_goal(&mut labels))
        {
            rendered.push_str("; goal: ");
            rendered.push_str(&goal);
        }
    }
    if failures.len() > 8 {
        rendered.push_str("\n    … <additional search candidates omitted>");
    }
    rendered.push_str(&labels.trace_legend());
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
    fn rejected_read_prerequisite_uses_the_shared_state_legend() {
        use crate::kernel::{Address, ProgramType, SymbolicMemory, Variable};
        struct Rejected(Proposition);
        impl ProofDiagnosticState for Rejected {
            fn failed_requirement(&self) -> Option<(&str, &Proposition)> {
                Some(("unproved prerequisite", &self.0))
            }
            fn kernel_goal(&self) -> Option<&Proposition> {
                None
            }
            fn premises(&self, _: usize) -> Vec<&Proposition> {
                Vec::new()
            }
            fn premise_count(&self) -> usize {
                0
            }
        }
        let state = Rejected(Proposition::MemoryReadDefined {
            at: None,
            memory: SymbolicMemory::new(),
            pointer: Address::symbolic(Variable(987_001)),
            value_type: ProgramType::Int32,
        });
        let mut labels = render::MemoryStateLabels::default();
        let report = render_failed_requirement(&state, &mut labels);
        assert!(report.contains("unproved prerequisite"), "{report}");
        assert!(
            report.contains("defined(at(<state A>, *<pointer A>))"),
            "{report}"
        );
        let legend = labels.trace_legend();
        assert!(legend.contains("<state A> is "), "{legend}");
        assert!(
            !report.contains("unsupported conditional proof"),
            "{report}"
        );
    }

    #[test]
    fn rejected_resource_fact_uses_one_printer_and_state_legend() {
        let _typed = render::TypedNotationScope::enter();
        use crate::kernel::{Address, ProgramType, SymbolicMemory, Variable};
        struct Rejected(crate::kernel::proof::RejectedResourceRewriteFact);
        impl ProofDiagnosticState for Rejected {
            fn rejected_resource_fact(
                &self,
            ) -> Option<&crate::kernel::proof::RejectedResourceRewriteFact> {
                Some(&self.0)
            }
            fn kernel_goal(&self) -> Option<&Proposition> {
                None
            }
            fn premises(&self, _: usize) -> Vec<&Proposition> {
                vec![]
            }
            fn premise_count(&self) -> usize {
                0
            }
        }
        let read = |memory| Proposition::MemoryReadDefined {
            at: None,
            memory,
            pointer: Address::symbolic(Variable(987_002)),
            value_type: ProgramType::Int32,
        };
        let rejected = read(SymbolicMemory::new());
        let allowed = read(SymbolicMemory::new().with_block("changed", 4));
        let state = Rejected(crate::kernel::proof::RejectedResourceRewriteFact {
            rejected: rejected.clone(),
            allowed: vec![allowed.clone(); 13].into(),
        });
        let mut labels = render::MemoryStateLabels::default();
        let report = render_failed_requirement(&state, &mut labels);
        assert!(
            report.starts_with(&format!(
                "rejected fact: {}",
                render::render_proposition_labeled(&rejected, &mut labels)
            )),
            "{report}"
        );
        assert!(
            report.contains(&render::render_proposition_labeled(&allowed, &mut labels)),
            "{report}"
        );
        assert!(
            report.contains("state#1") && report.contains("state#2"),
            "{report}"
        );
        assert!(report.contains("1 more allowed fact"), "{report}");
        let legend = labels.trace_legend();
        assert!(
            legend.contains("state#1 =") && legend.contains("state#2 ="),
            "{legend}"
        );
    }

    #[test]
    fn rendering_is_the_boundary_that_visits_retained_context() {
        let state = Arc::new(CountingState {
            goal: Proposition::condition_is(crate::kernel::ConditionTerm::Constant(true), true),
            calls: AtomicUsize::new(0),
        });
        let diagnostic = ProofFailureDiagnostic {
            failing_path: None,
            checks: None,
            origin: ProofDiagnosticOrigin {
                stage: crate::surface::proof_diagnostics::ProofDiagnosticStage::CheckedStep,
                location: "source tactic 4".into(),
                source_tactic_path: None,
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
    fn trace_context_retains_a_refined_integer_goal_without_a_source_spelling() {
        use crate::kernel::{
            ConditionTerm, IntegerTerm, MachineIntegerType, MachineTerm, Variable,
        };
        let goal = Proposition::condition_is(
            ConditionTerm::integer_equal(
                IntegerTerm::from_machine(
                    MachineIntegerType::Int32,
                    MachineTerm::Variable(Variable(981_701)),
                )
                .unwrap(),
                IntegerTerm::constant_i64(7),
            ),
            true,
        );
        let state = Arc::new(CountingState {
            goal,
            calls: AtomicUsize::new(0),
        });
        let diagnostic = ProofFailureDiagnostic {
            failing_path: None,
            checks: None,
            origin: ProofDiagnosticOrigin {
                stage: crate::surface::proof_diagnostics::ProofDiagnosticStage::CheckedStep,
                location: "source tactic 4".into(),
                source_tactic_path: None,
            },
            claim_label: "word.contract".into(),
            reason: "reason".into(),
            state: Some(state),
        };
        crate::surface::with_proof_trace("word", || {
            let report = render_trace_context_labeled(
                &diagnostic,
                &[],
                &mut render::MemoryStateLabels::default(),
            );
            assert!(report.contains("machine-integer<Int32>"), "{report}");
            assert_eq!(
                report.matches("machine-integer<Int32>").count(),
                2,
                "{report}"
            );
            assert_eq!(
                report
                    .lines()
                    .filter(|line| line.starts_with("goal:"))
                    .count(),
                1,
                "{report}"
            );
            assert!(report.contains("premises in scope"), "{report}");
            assert!(report.len() < 2048, "{report}");
        });
    }

    #[test]
    fn click_error_lazily_caches_and_preserves_structured_context() {
        let state = Arc::new(CountingState {
            goal: Proposition::condition_is(crate::kernel::ConditionTerm::Constant(true), true),
            calls: AtomicUsize::new(0),
        });
        let diagnostic = ProofFailureDiagnostic {
            failing_path: None,
            checks: None,
            origin: ProofDiagnosticOrigin {
                stage: crate::surface::proof_diagnostics::ProofDiagnosticStage::Other("step"),
                location: "source tactic 44".into(),
                source_tactic_path: None,
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
    fn reported_trace_uses_the_goals_state_labels() {
        use crate::kernel::{Address, AddressBase, AddressOffset, MachineTerm, SymbolicMemory};

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
                labels: &mut render::MemoryStateLabels,
                tactic_location: &dyn Fn(
                    &[usize],
                )
                    -> Option<(String, crate::source::SourcePosition)>,
                branch_arm: &dyn Fn(&[usize], &crate::source::SourcePosition) -> Option<usize>,
                have_body_contains: &dyn Fn(&[usize], &crate::source::SourcePosition) -> bool,
                target: Option<&crate::source::SourcePosition>,
                failing_path: Option<usize>,
            ) -> Option<String> {
                crate::surface::proof_trace::render(
                    claim,
                    &[crate::surface::proof_trace::TracePathNode {
                        node: 1,
                        selected_arm: None,
                    }],
                    labels,
                    tactic_location,
                    branch_arm,
                    have_body_contains,
                    target,
                    failing_path,
                )
            }
        }
        let at = |memory| Proposition::MemoryLoadable {
            memory,
            base: Address {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::Constant(0),
            },
            bytes: (MachineTerm::constant(1)).into(),
            wide: false,
        };
        crate::surface::with_proof_trace("f", || {
            let memory = SymbolicMemory::new().with_block("shared", 1);
            crate::surface::proof_trace::record(
                1,
                crate::surface::proof_trace::TraceStep {
                    header: "\n    source tactic 0: step".into(),
                    source_tactic_path: None,
                    call_source: None,
                    facts: vec![crate::surface::proof_trace::TraceFact {
                        kernel: at(memory.clone()),
                    }],
                    more_facts: 0,
                    frontier: None,
                    load: None,
                    read_equalities: Vec::new(),
                    read_context_changed: false,
                    transport: None,
                    resources: Vec::new(),
                    more_resources: 0,
                    origin: None,
                    chosen: None,
                    forgotten_cells: Vec::new(),
                    history_stops: Vec::new(),
                },
            );
            let diagnostic = ProofFailureDiagnostic {
                failing_path: None,
                checks: None,
                origin: ProofDiagnosticOrigin {
                    stage: crate::surface::proof_diagnostics::ProofDiagnosticStage::CheckedStep,
                    location: "source tactic 1".into(),
                    source_tactic_path: None,
                },
                claim_label: "f.contract".into(),
                reason: "failed".into(),
                state: Some(Arc::new(TracedState(at(memory)))),
            };
            let report = crate::surface::ClickError::with_diagnostic("failed", diagnostic).report();
            assert!(report.contains("goal: viewable(memory=state#1"), "{report}");
            assert!(report.contains("adds: viewable(memory=state#1"), "{report}");
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
                premise_excerpt: None,
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
            goal: Proposition::condition_is(crate::kernel::ConditionTerm::Constant(true), true),
            calls: AtomicUsize::new(0),
        });
        let diagnostic = Arc::new(ProofFailureDiagnostic {
            failing_path: None,
            checks: None,
            origin: ProofDiagnosticOrigin {
                stage: crate::surface::proof_diagnostics::ProofDiagnosticStage::CheckedStep,
                location: "loop closure".into(),
                source_tactic_path: None,
            },
            claim_label: "claim".into(),
            reason: "leaf remained open".into(),
            state: Some(state),
        });
        let report = render_terminal_message(
            "closure failed",
            &ProofFailureDiagnostic {
                failing_path: None,
                checks: None,
                origin: ProofDiagnosticOrigin {
                    stage: crate::surface::proof_diagnostics::ProofDiagnosticStage::CheckedStep,
                    location: "loop closure".into(),
                    source_tactic_path: None,
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
                premise_excerpt: None,
            }],
        );
        assert!(report.contains("[UnclosedGoal]"));
        assert!(report.contains("goal: true"));
    }
    fn unspelled_test_fact(variable: crate::kernel::Variable) -> Proposition {
        Proposition::condition_is(
            crate::kernel::ConditionTerm::Compare {
                format: crate::kernel::MachineIntegerType::Int32,
                relation: crate::kernel::CompareRelation::Equal,
                left: Box::new(crate::kernel::MachineTerm::Variable(variable)),
                right: Box::new(crate::kernel::MachineTerm::constant(0)),
            },
            true,
        )
    }

    fn unspelled_test_failure(premises: &[Proposition]) -> ProofSearchFailure {
        ProofSearchFailure {
            strategy: "solve premise raising".into(),
            reason: "selected premises were omitted: ".into(),
            kind: "NotApplicable".into(),
            diagnostic: None,
            premise_excerpt: Some(ProofSearchPremiseExcerpt::new(
                &premises.iter().collect::<Vec<_>>(),
            )),
        }
    }

    #[test]
    fn unspelled_premises_use_terminal_names_and_keep_the_reason_bound() {
        let variable = crate::kernel::Variable(786_900);
        let mut failure = unspelled_test_failure(&[unspelled_test_fact(variable)]);
        let mut labels = render::MemoryStateLabels::default();
        labels.source_name(variable, "prefix_total".into());
        let reason = render_search_reason(&failure, &mut labels);
        assert!(reason.contains("prefix_total"), "{reason}");
        assert!(!reason.contains("<unnamed"), "{reason}");
        failure.reason = "é".repeat(MAX_SEARCH_REASON_BYTES);
        let reason = render_search_reason(&failure, &mut labels);
        assert!(reason.len() <= MAX_SEARCH_REASON_BYTES);
        assert!(reason.is_char_boundary(reason.len()));
    }

    #[test]
    fn unspelled_premises_keep_entry_names_after_the_session_unwinds() {
        use crate::kernel::{MachineTerm, ProgramExpression, ProgramValue, Variable};
        use crate::languages::interface::{ImportedParameter, InterfaceType};

        let variable = Variable(786_901);
        let parameters = [ImportedParameter::new(
            InterfaceType::Int32,
            "input".into(),
            None,
        )];
        let arguments = [ProgramExpression::Value(ProgramValue::Int32(
            MachineTerm::Variable(variable),
        ))];
        render::enter_ambient_naming(
            crate::surface::ParameterBinding::new(&parameters, &arguments),
            &crate::kernel::ExecutionState::new(),
        );
        let failure = unspelled_test_failure(&[unspelled_test_fact(variable)]);
        render::clear_ambient_naming();
        let report = render_search_failures("failed", std::slice::from_ref(&failure));
        assert!(report.contains("input"), "{report}");
        assert!(!report.contains("<unnamed"), "{report}");

        let preferred = [ImportedParameter::new(
            InterfaceType::Int32,
            "loop_value".into(),
            None,
        )];
        let mut labels = render::MemoryStateLabels::naming(crate::surface::ParameterBinding::new(
            &preferred, &arguments,
        ));
        let reason = render_search_reason(&failure, &mut labels);
        assert!(reason.contains("loop_value"), "{reason}");
        assert!(!reason.contains("input"), "{reason}");
    }

    #[test]
    fn unspelled_premise_capture_is_bounded_across_selected_sizes() {
        for size in [8, 16, 32, 64] {
            let premises = (0..size)
                .map(|index| unspelled_test_fact(crate::kernel::Variable(786_910 + index)))
                .collect::<Vec<_>>();
            let references = premises.iter().collect::<Vec<_>>();
            let (excerpt, work) = crate::instrumentation::measure_deterministic_work(|| {
                ProofSearchPremiseExcerpt::new(&references)
            });
            assert_eq!(excerpt.premises.len(), 4);
            assert_eq!(excerpt.remaining, size as usize - 4);
            assert!(work <= 64, "{size} selected facts: {work} capture work");
        }
    }
}
