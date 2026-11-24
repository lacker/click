//! Opt-in observations of checked proof steps for CLI diagnostics.
//! The trace is diagnostic only; no recorded text participates in checking.

use crate::kernel::proof::BranchId;
use crate::kernel::{Address, ConditionTerm, MachineTerm, Proposition, SharedMemory};
#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::source::SourcePosition;
use crate::surface::proof_diagnostics::ProofDiagnosticState;
use crate::surface::proof_diagnostics::render::{self, MemoryStateLabels};
use std::any::Any;
use std::cell::{Cell, LazyCell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

struct Capture {
    function: String,
    node_keys: HashMap<usize, Box<dyn Any>>,
    steps: HashMap<usize, TraceStep>,
    branches: HashMap<usize, TraceBranch>,
    joins: HashMap<usize, TraceJoin>,
    bodies: HashMap<usize, TraceBody>,
    matches: HashMap<usize, TraceMatch>,
    scope_parents: HashMap<usize, TraceScope>,
    retained_paths: Vec<TraceRetainedPath>,
}

struct TraceRetainedPath {
    names: Option<Box<dyn ProofDiagnosticState>>,
    claim: String,
    completed: bool,
    /// A loop phase's path, recorded while the function's own
    /// path is still being driven. It is rendered only for a target that
    /// lies on it; a plain trace shows the function's path.
    nested: bool,
    path_index: usize,
    lineage: Vec<TracePathNode>,
    /// Retain the checked lineage chain until the CLI has rendered it.
    _retained: Box<dyn Any>,
}

/// Share a persistent proof path; walk it only if the report needs this scope.
/// Eagerly copying the preceding path for every `have` takes quadratic storage.
pub(super) type TraceLineage =
    Rc<LazyCell<Vec<TracePathNode>, Box<dyn FnOnce() -> Vec<TracePathNode>>>>;

pub(super) fn deferred_lineage(
    build: impl FnOnce() -> Vec<TracePathNode> + 'static,
) -> TraceLineage {
    Rc::new(LazyCell::new(Box::new(build)))
}

#[cfg(test)]
thread_local! {
    static LINEAGE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn record_lineage_visit() {
    LINEAGE_VISITS.with(|visits| visits.set(visits.get() + 1));
}

#[cfg(test)]
pub(super) fn lineage_visits() -> usize {
    LINEAGE_VISITS.with(std::cell::Cell::get)
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
    /// How many function outcome paths each arm of a terminal join
    /// contributes, then-arm paths first; `None` for a join whose arms
    /// continue. Recorded only while tracing, it selects the arm that holds
    /// a failing path.
    pub arm_paths: Option<[usize; 2]>,
    /// Keeps arm evidence alive so later proof attempts cannot recycle its
    /// pointer identities.
    pub _retained: Box<dyn Any>,
}

struct TraceScope {
    lineage: TraceLineage,
    _retained: Box<dyn Any>,
}

pub(super) struct TraceMatch {
    pub header: String,
    pub source_tactic_path: Option<Vec<usize>>,
    pub arms: Vec<Option<TraceMatchArm>>,
}

pub(super) struct TraceMatchArm {
    pub names: Box<dyn ProofDiagnosticState>,
    pub name: String,
    pub fact: TraceFact,
    pub lineage: Vec<TracePathNode>,
    pub _retained: Box<dyn Any>,
}

pub(super) fn record_match(node: usize, trace: TraceMatch) {
    CAPTURE.with(|slot| {
        if let Some(capture) = slot.borrow_mut().as_mut() {
            capture.matches.insert(node, trace);
        }
    });
}

pub(super) struct TraceBody {
    pub lineage: Vec<TracePathNode>,
    pub _retained: Box<dyn Any>,
}

pub(super) struct TraceBranch {
    pub header: String,
    pub source_tactic_path: Option<Vec<usize>>,
    /// How the source spells the two arms: `then`/`else` for an `if`,
    /// `left`/`right` for `cases` and `both`.
    pub arm_names: [&'static str; 2],
    pub arms: [(BranchId, Vec<TraceFact>); 2],
}

pub(super) struct TraceStep {
    pub header: String,
    pub source_tactic_path: Option<Vec<usize>>,
    pub call_source: Option<TraceCallSource>,
    pub facts: Vec<TraceFact>,
    pub more_facts: usize,
    pub frontier: Option<String>,
    pub load: Option<TraceLoad>,
    pub read_equalities: Vec<TraceFact>,
    pub read_context_changed: bool,
    pub transport: Option<[TraceFact; 2]>,
    pub resources: Vec<TraceResourceChange>,
    pub more_resources: usize,
    /// The written smart tactic, or elided form, whose search produced this
    /// step ([`smart_origin`]); `None` for a step the script wrote.
    pub origin: Option<&'static str>,
    /// The step as `click expand` would write it, when a search chose one of
    /// its arguments (a `using` list).
    pub chosen: Option<String>,
    /// Cached cells this step's stores dropped, each beside the cell it
    /// wrote, with the index disequality the store reads to keep one.
    pub forgotten_cells: Vec<TraceForgottenCell>,
    /// Read-history walks this step made that stopped without reaching the
    /// value: at the one transition a read follows, or at one not shown
    /// separate.
    pub history_stops: Vec<crate::kernel::TransportCellWalkDiagnostic>,
}

/// A cached cell a checked step's store dropped. Read from the step's own
/// memory delta, the same bounded inspection the implicit tail's store
/// search makes; the store itself records nothing.
pub(super) struct TraceForgottenCell {
    pub cell: Address,
    pub store: Address,
    /// The two cells as the statement's C locals spelled them, `q[0]`.
    pub spelled: [Option<String>; 2],
    pub indices_differ: Proposition,
}

/// Values observed at one accepted load statement. The retained theorem's
/// entry state supplies the state; the outcome supplies the produced value.
pub(super) struct TraceLoad {
    pub target: String,
    pub value: crate::kernel::ProgramValue,
    pub address: crate::kernel::ProgramValue,
    pub memory: SharedMemory,
}

impl TraceLoad {
    fn append(&self, output: &mut String, labels: &mut MemoryStateLabels, indent: &str) {
        let retained_state = labels.memory_state_name(self.memory.memory());
        let identity =
            |value: &crate::kernel::ProgramValue, labels: &mut MemoryStateLabels| match value {
                crate::kernel::ProgramValue::Pointer(pointer) => {
                    labels.pointer_value_name(pointer.address())
                }
                _ => render::render_program_value_labeled(value, labels),
            };
        let value = identity(&self.value, labels);
        let address = identity(&self.address, labels);
        output.push_str(&format!(
            "\n{indent}produces {} = {value}\n{indent}read: load_function_pointer({address}) in {retained_state}",
            trace_text(&self.target, 240),
        ));
    }
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
}

/// Source spelling recovered against the read's own state. The memory is
/// retained until report rendering so unnamed states share report labels.
#[derive(Clone)]
pub(super) struct PointerTraceView {
    pub text: String,
    pub retained_state: Option<(SharedMemory, Option<String>)>,
}

impl PointerTraceView {
    fn render(&self, labels: &mut MemoryStateLabels) -> String {
        let text = trace_text(&self.text, 240);
        match &self.retained_state {
            Some((_, Some(point))) => format!("at({}, {text})", trace_text(point, 128)),
            Some((memory, None)) => {
                format!("{text} in {}", labels.memory_state_name(memory.memory()))
            }
            None => text,
        }
    }
}

/// Diagnostic-only payload for the exact rejected pair. Related equalities
/// are bounded explicit aliases, not a proof-search result or proposed fix.
pub(super) struct ChildArgumentTrace {
    child: String,
    index: usize,
    actual: Address,
    required: Address,
    related: Vec<Address>,
    views: HashMap<Address, PointerTraceView>,
}

impl ChildArgumentTrace {
    pub(super) fn from_refusal(
        refusal: &crate::kernel::ResourceRewriteRefusal,
        assumptions: &crate::kernel::PureFactContext,
    ) -> Option<Self> {
        let crate::kernel::ResourceRewriteRefusal::ChildArgumentNotEstablished {
            child,
            index,
            actual,
            required,
        } = refusal
        else {
            return None;
        };
        let (
            Some(crate::kernel::ProgramValue::Pointer(actual)),
            Some(crate::kernel::ProgramValue::Pointer(required)),
        ) = (actual.as_program_value(), required.as_program_value())
        else {
            return None;
        };
        Some(Self {
            views: HashMap::new(),
            child: child.clone(),
            index: *index,
            actual: actual.address().clone(),
            required: required.address().clone(),
            related: assumptions
                .exact_pointer_aliases(actual.address())
                .take(4)
                .cloned()
                .collect(),
        })
    }

    pub(super) fn name_values(
        &mut self,
        mut name: impl FnMut(&Address, &Address) -> Option<[PointerTraceView; 2]>,
    ) {
        for other in std::iter::once(&self.required).chain(&self.related) {
            if let Some([actual, required]) = name(&self.actual, other) {
                self.views.insert(self.actual.clone(), actual);
                self.views.insert(other.clone(), required);
            }
        }
    }

    fn value(&self, pointer: &Address, labels: &mut MemoryStateLabels) -> String {
        if let Some(view) = self.views.get(pointer) {
            view.render(labels)
        } else if pointer == &Address::null() {
            "0 (null pointer)".into()
        } else if let Some(MachineTerm::MemoryLoad(memory, address, _)) =
            pointer_definition(pointer)
        {
            format!(
                "pointer_read(address {}, memory {})",
                labels.pointer_value_name(&address),
                labels.memory_state_name(memory.memory())
            )
        } else {
            labels.pointer_value_name(pointer)
        }
    }

    pub(super) fn append_to(&self, trace: &mut String, labels: &mut MemoryStateLabels) {
        let comparison = self.render(labels);
        trace.push_str(&comparison);
    }

    pub(super) fn render(&self, labels: &mut MemoryStateLabels) -> String {
        let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
        let actual = self.value(&self.actual, labels);
        let required = self.value(&self.required, labels);
        let mut output = format!(
            "\n\n  failed child argument comparison (checked):\n    child `{}`, argument {}\n    supplied: {actual}\n    required: {required}\n    equality was not established",
            trace_text(&self.child, 128),
            self.index + 1
        );
        if !self.related.is_empty() {
            output.push_str(
                "\n    potentially relevant known equalities (selected by shared supplied value):",
            );
            for pointer in &self.related {
                let fact = Proposition::condition_is(
                    ConditionTerm::address_equal(self.actual.clone(), pointer.clone()),
                    true,
                );
                output.push_str(&format!(
                    "\n      {}",
                    render::render_proposition_labeled(&fact, labels)
                ));
            }
            output.push_str(
                "\n    selection is diagnostic guidance, not an explanation of why equality failed",
            );
        }
        output.push_str("\n    defining memory states identify original reads; different states alone do not establish unequal values");
        output
    }
}

pub(super) fn pointer_definition(pointer: &Address) -> Option<MachineTerm> {
    crate::kernel::logical_pointer_read_term(pointer).or_else(|| {
        let read = pointer.as_loaded_value()?;
        (read.displacement == crate::kernel::AddressOffset::Constant(0)).then(|| {
            crate::kernel::MachineTerm::read_named(
                crate::kernel::ProgramPoint::at(&read.defining_memory),
                read.defining_address,
                crate::kernel::LoadKind::Int32,
            )
        })
    })
}

/// The generated equation connecting a canonical load value to its raw
/// memory read is checker bookkeeping, not an additional surface premise.
/// The surface condition that caused the read is reported separately.
/// Kernel authority is no proof-state fact at all.
pub(super) fn visible_checked_fact(fact: &Proposition) -> bool {
    !crate::kernel::is_load_variable_defining_fact(fact) && !fact.is_kernel_authority()
}

thread_local! {
    static CAPTURE: RefCell<Option<Capture>> = const { RefCell::new(None) };
    static IMPLICIT_STEP: Cell<Option<&'static str>> = const { Cell::new(None) };
    /// The written tactics running under a trace, innermost last: the name
    /// of a smart tactic or elided form, or `None` for a simple tactic,
    /// whose checked steps are its own.
    static ORIGINS: RefCell<Vec<Option<&'static str>>> = const { RefCell::new(Vec::new()) };
}

/// Attributes checked steps and errors to the proof operation running them.
pub(super) struct TraceOrigin {
    tracing: bool,
    previous_implicit_step: Option<&'static str>,
}

impl TraceOrigin {
    pub(super) fn enter(smart: Option<&'static str>) -> Self {
        Self::enter_step(smart, None)
    }

    pub(super) fn enter_implicit(step: &'static str) -> Self {
        Self::enter_step(Some(step), Some(step))
    }

    fn enter_step(smart: Option<&'static str>, implicit_step: Option<&'static str>) -> Self {
        let tracing = CAPTURE.with(|slot| slot.borrow().is_some());
        if tracing {
            ORIGINS.with(|origins| origins.borrow_mut().push(smart));
        }
        Self {
            tracing,
            previous_implicit_step: IMPLICIT_STEP.replace(implicit_step),
        }
    }
}

impl Drop for TraceOrigin {
    fn drop(&mut self) {
        if self.tracing {
            ORIGINS.with(|origins| origins.borrow_mut().pop());
        }
        IMPLICIT_STEP.set(self.previous_implicit_step);
    }
}

/// The current implicit operation, even when proof tracing is disabled.
pub(super) fn implicit_step() -> Option<&'static str> {
    IMPLICIT_STEP.get()
}

/// The smart tactic or elided form whose search is checking steps now: the
/// innermost written tactic, when it is one.
pub(super) fn smart_origin() -> Option<&'static str> {
    ORIGINS.with(|origins| origins.borrow().last().copied().flatten())
}

/// Scope tracing to one named function on the verification thread.
pub fn with_proof_trace<R>(function: &str, verify: impl FnOnce() -> R) -> R {
    #[cfg(test)]
    LINEAGE_VISITS.with(|visits| visits.set(0));
    struct Restore(Option<Capture>);
    impl Drop for Restore {
        fn drop(&mut self) {
            CAPTURE.with(|slot| *slot.borrow_mut() = self.0.take());
        }
    }
    let prior = CAPTURE.with(|slot| {
        slot.replace(Some(Capture {
            function: function.to_owned(),
            node_keys: HashMap::new(),
            steps: HashMap::new(),
            branches: HashMap::new(),
            joins: HashMap::new(),
            bodies: HashMap::new(),
            matches: HashMap::new(),
            scope_parents: HashMap::new(),
            retained_paths: Vec::new(),
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

/// Keep a recorded node's allocation reserved until the trace ends. A discarded
/// search candidate can drop its node and ancestors immediately, but a later
/// checked node must never inherit its observations through address reuse.
pub(super) fn trace_node_key<T: 'static>(node: &Arc<T>) -> usize {
    let key = Arc::as_ptr(node) as usize;
    CAPTURE.with(|slot| {
        if let Some(capture) = slot.borrow_mut().as_mut() {
            capture
                .node_keys
                .entry(key)
                .or_insert_with(|| Box::new(Arc::downgrade(node)));
        }
    });
    key
}

pub(super) fn has_recorded_step(node: usize) -> bool {
    CAPTURE.with(|slot| {
        slot.borrow()
            .as_ref()
            .is_some_and(|capture| capture.steps.contains_key(&node))
    })
}

pub(super) fn record(node: usize, step: TraceStep) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        capture.steps.insert(node, step);
    });
}

pub(super) fn record_branch(node: usize, branch: TraceBranch) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        capture.branches.insert(node, branch);
    });
}

pub(super) fn record_join(node: usize, join: TraceJoin) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        capture.joins.insert(node, join);
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
        capture.bodies.insert(node, body);
    });
}

thread_local! {
    static LOOP_PARENT_LINEAGE: RefCell<Option<TraceLineage>> = const { RefCell::new(None) };
}

/// Runs `verify` with `lineage`, the traced proof's path up to a `loop`
/// tactic, on record as the parent of any loop phase proof it drives, so
/// the phase's own trace can be rendered with that path above it.
pub(crate) fn with_loop_parent_lineage<R>(
    lineage: Option<TraceLineage>,
    verify: impl FnOnce() -> R,
) -> R {
    struct Restore(Option<TraceLineage>);
    impl Drop for Restore {
        fn drop(&mut self) {
            LOOP_PARENT_LINEAGE.with(|slot| *slot.borrow_mut() = self.0.take());
        }
    }
    let prior = LOOP_PARENT_LINEAGE.with(|slot| slot.replace(lineage));
    let _restore = Restore(prior);
    verify()
}

/// The traced path up to the `loop` tactic whose phase proof is being
/// driven, if a trace is on and the tactic lies on one.
pub(crate) fn loop_parent_lineage() -> Option<TraceLineage> {
    LOOP_PARENT_LINEAGE.with(|slot| slot.borrow().clone())
}

pub(super) fn register_scope(root: usize, parent_lineage: TraceLineage, retained: Box<dyn Any>) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        capture.scope_parents.insert(
            root,
            TraceScope {
                lineage: parent_lineage,
                _retained: retained,
            },
        );
    });
}

pub(super) fn record_accepted_path(
    claim: &str,
    path_index: usize,
    nested: bool,
    lineage: Vec<TracePathNode>,
    retained: Box<dyn Any>,
    names: Option<Box<dyn ProofDiagnosticState>>,
) {
    record_retained_path(claim, path_index, nested, true, lineage, retained, names);
}

pub(super) fn record_unfinished_path(
    claim: &str,
    path_index: usize,
    lineage: Vec<TracePathNode>,
    retained: Box<dyn Any>,
    names: Option<Box<dyn ProofDiagnosticState>>,
) {
    record_retained_path(claim, path_index, true, false, lineage, retained, names);
}

/// Written steps preceding a refused contract completion are a checked prefix,
/// not an accepted path and not an abandoned search candidate.
pub(super) fn record_certification_failure_path(
    claim: &str,
    path_index: usize,
    lineage: Vec<TracePathNode>,
    retained: Box<dyn Any>,
    names: Option<Box<dyn ProofDiagnosticState>>,
) {
    record_retained_path(claim, path_index, false, false, lineage, retained, names);
}

fn record_retained_path(
    claim: &str,
    path_index: usize,
    nested: bool,
    completed: bool,
    lineage: Vec<TracePathNode>,
    retained: Box<dyn Any>,
    names: Option<Box<dyn ProofDiagnosticState>>,
) {
    CAPTURE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(capture) = slot.as_mut() else { return };
        capture.retained_paths.push(TraceRetainedPath {
            names,
            claim: claim.to_owned(),
            completed,
            nested,
            path_index,
            lineage,
            _retained: retained,
        });
    });
}

/// Walk the accepted proof lineage. A structural join carries the checked
/// arm lineages it replaced, so an earlier call remains visible without
/// including abandoned smart-search candidates.
pub(super) fn render(
    claim: &str,
    lineage: &[TracePathNode],
    labels: &mut MemoryStateLabels,
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
    failing_path: Option<usize>,
) -> Option<String> {
    let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
    CAPTURE.with(|slot| {
        let slot = slot.borrow();
        let capture = slot.as_ref()?;
        if !enabled_for(claim) {
            return None;
        }
        let (mut report, reached) = render_lineage(
            capture,
            lineage,
            labels,
            tactic_location,
            branch_arm,
            have_body_contains,
            target,
            failing_path,
        );
        if let Some(target) = target
            && !reached
        {
            // A failing loop phase can have already checked a sibling arm.
            // Only retained checked paths may answer a target outside the
            // failure's own lineage; recorded search candidates cannot.
            for path in capture
                .retained_paths
                .iter()
                .filter(|path| path.claim == claim)
            {
                let mut path_labels = MemoryStateLabels::default();
                if let Some(names) = &path.names {
                    names.register_names(&mut path_labels);
                }
                let (alternative, reached) = render_lineage(
                    capture,
                    &path.lineage,
                    &mut path_labels,
                    tactic_location,
                    branch_arm,
                    have_body_contains,
                    Some(target),
                    None,
                );
                if reached {
                    *labels = path_labels;
                    return Some(alternative);
                }
            }
            report.push_str("\n    target tactic has no recorded checked step on a retained path");
        }
        Some(report)
    })
}

/// Render a completed proof only from paths retained after checked path
/// certification. A target inside one path selects that path; without a
/// target, the first accepted path is a representative execution route.
pub(crate) fn render_accepted(
    labels: &mut MemoryStateLabels,
    tactic_location: &dyn Fn(&str, &[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&str, &[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&str, &[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
) -> Option<String> {
    let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
    CAPTURE.with(|slot| {
        let slot = slot.borrow();
        let capture = slot.as_ref()?;
        // The function's own paths first; a loop phase's path only answers a
        // target that lies inside the phase.
        let paths = capture
            .retained_paths
            .iter()
            .rev()
            .filter(|path| !path.completed && !path.nested)
            .chain(
                capture
                    .retained_paths
                    .iter()
                    .filter(|path| path.completed && !path.nested),
            )
            .chain(
                capture
                    .retained_paths
                    .iter()
                    .filter(|path| path.completed && path.nested && target.is_some()),
            );
        for path in paths {
            let locate = |indices: &[usize]| tactic_location(&path.claim, indices);
            let arm = |indices: &[usize], position: &SourcePosition| {
                branch_arm(&path.claim, indices, position)
            };
            let body = |indices: &[usize], position: &SourcePosition| {
                have_body_contains(&path.claim, indices, position)
            };
            let mut path_labels = if path.completed {
                MemoryStateLabels::default()
            } else {
                // The rejected fact was printed before this prefix. Its
                // state and value identities must remain the same here.
                labels.clone()
            };
            if let Some(names) = &path.names {
                names.register_names(&mut path_labels);
            }
            let (mut report, reached) = render_lineage(
                capture,
                &path.lineage,
                &mut path_labels,
                &locate,
                &arm,
                &body,
                target,
                None,
            );
            if target.is_none() || reached {
                *labels = path_labels;
                if !path.completed {
                    report = report.replacen(
                        "proof trace (checked tactics and branch facts)",
                        "proof trace (checked prefix; certification failed)",
                        1,
                    );
                } else if capture
                    .retained_paths
                    .iter()
                    .filter(|path| path.completed && !path.nested)
                    .count()
                    > 1
                {
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

/// `failing_path` is the index of the function outcome path a failure
/// lies on, when the failure names one: a terminal join shows the arm that
/// holds it.
fn render_lineage(
    capture: &Capture,
    lineage: &[TracePathNode],
    labels: &mut MemoryStateLabels,
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
    failing_path: Option<usize>,
) -> (String, bool) {
    let mut output = String::from("  proof trace (checked tactics and branch facts):");
    let mut segments = vec![lineage];
    let mut roots = HashSet::new();
    while let Some(root) = segments.last().and_then(|segment| segment.first()) {
        if !roots.insert(root.node) {
            break;
        }
        let Some(parent) = capture.scope_parents.get(&root.node) else {
            break;
        };
        segments.push(&parent.lineage);
    }
    let mut shown = 0;
    let mut depth = 0;
    let mut done = false;
    let mut reached = false;
    let segment_count = segments.len();
    for (index, segment) in segments.into_iter().rev().enumerate() {
        depth = append_path(
            &mut output,
            capture,
            segment,
            labels,
            tactic_location,
            branch_arm,
            have_body_contains,
            target,
            failing_path,
            depth,
            &mut shown,
            &mut done,
            &mut reached,
        );
        // An enclosing segment stops at its first step past the target,
        // which for a loop phase's path is the enclosing proof's step after
        // the loop; the phase's own segment still lies ahead and is where
        // the target is reached.
        if done && !reached && index + 1 < segment_count {
            done = false;
            depth += 1;
            continue;
        }
        if done {
            break;
        }
    }
    if shown == 0 {
        output.push_str("\n    <no checked simple steps recorded on this path>");
    }
    (output, reached)
}

fn append_path(
    output: &mut String,
    capture: &Capture,
    lineage: &[TracePathNode],
    labels: &mut MemoryStateLabels,
    tactic_location: &dyn Fn(&[usize]) -> Option<(String, SourcePosition)>,
    branch_arm: &dyn Fn(&[usize], &SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&[usize], &SourcePosition) -> bool,
    target: Option<&SourcePosition>,
    failing_path: Option<usize>,
    mut depth: usize,
    shown: &mut usize,
    done: &mut bool,
    reached: &mut bool,
) -> usize {
    for path_node in lineage {
        if *done {
            break;
        }
        let indent = " ".repeat(2 + depth * 2);
        let mut detail = String::new();
        if let Some(matched) = capture.matches.get(&path_node.node) {
            let site = matched
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
            let selected = target
                .and_then(|target| {
                    matched
                        .source_tactic_path
                        .as_deref()
                        .and_then(|path| branch_arm(path, target))
                })
                .or_else(|| matched.arms.iter().position(Option::is_some));
            if let Some(arm) = selected
                .and_then(|index| matched.arms.get(index))
                .and_then(Option::as_ref)
            {
                arm.names.register_names(labels);
                output.push_str(&format!(
                    "\n{indent}{} ({} arm)",
                    trace_header(
                        &matched.header,
                        matched.source_tactic_path.as_deref(),
                        tactic_location
                    ),
                    arm.name
                ));
                append_added_facts(
                    output,
                    std::slice::from_ref(&arm.fact),
                    labels,
                    &format!("{indent}  "),
                );
                *shown += 1;
                if target.is_some_and(|target| {
                    site.as_ref().is_some_and(|(_, at)| source_same(at, target))
                }) {
                    *reached = true;
                }
                append_path(
                    output,
                    capture,
                    &arm.lineage,
                    labels,
                    tactic_location,
                    branch_arm,
                    have_body_contains,
                    target,
                    None,
                    depth + 1,
                    shown,
                    done,
                    reached,
                );
            }
            continue;
        }
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
                // A failure on one outcome path of a terminal join lies in
                // the arm that contributed that path; within the arm, its
                // index counts from the arm's first path.
                let failing_arm = failing_path.zip(join.arm_paths).and_then(|(path, counts)| {
                    if path < counts[0] {
                        Some((0, path))
                    } else {
                        (path - counts[0] < counts[1]).then(|| (1, path - counts[0]))
                    }
                });
                let continues = selected_arm.is_none() && failing_arm.is_some();
                let selected_arm = selected_arm.or(failing_arm.map(|(arm, _)| arm));
                if let Some(arm) = selected_arm {
                    let arm_failing_path = match failing_arm {
                        Some((failing, index)) if failing == arm => Some(index),
                        _ if join.arm_paths.is_none() => failing_path,
                        _ => None,
                    };
                    detail.push_str(&format!(
                        "\n{indent}{header} ({} arm)",
                        branch.arm_names[arm]
                    ));
                    append_added_facts(
                        &mut detail,
                        &branch.arms[arm].1,
                        labels,
                        &format!("{indent}  "),
                    );
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
                        arm_failing_path,
                        depth + 1,
                        shown,
                        done,
                        reached,
                    );
                    // The arm a target selected ran the rest of the source;
                    // the arm a failing path selected ends at function exit,
                    // and the outcome proof's own steps follow the join.
                    if !continues {
                        *done = true;
                    }
                } else {
                    detail.push_str(&format!("\n{indent}{header} (joined)"));
                    append_added_facts(&mut detail, &join.facts, labels, &format!("{indent}  "));
                    if join.more_facts > 0 {
                        detail.push_str(&format!(
                            "\n{indent}  … {} more joined facts",
                            join.more_facts
                        ));
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
                branch.arm_names[arm],
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
            let header = trace_header(
                step.header.trim(),
                step.source_tactic_path.as_deref(),
                tactic_location,
            );
            let origin = step
                .origin
                .filter(|origin| {
                    header
                        .rsplit_once(": ")
                        .is_none_or(|(_, kind)| kind != *origin)
                })
                .map(|origin| format!(" (from `{origin}`)"))
                .unwrap_or_default();
            detail.push_str(&format!(
                "\n{indent}{}",
                trace_text(&format!("{header}{origin}"), 240)
            ));
            let detail_indent = format!("{indent}  ");
            if let Some(chosen) = &step.chosen {
                detail.push_str(&format!(
                    "\n{detail_indent}chosen: {}",
                    trace_text(chosen, 480)
                ));
            }
            if let Some([source, target]) = &step.transport {
                for (name, fact) in [("source", source), ("target", target)] {
                    detail.push_str(&format!(
                        "\n{detail_indent}checked transport {name}: {}",
                        render::render_proposition_labeled(&fact.kernel, labels),
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
                detail.push_str(&format!("\n{detail_indent}{}", trace_text(frontier, 240)));
            }
            if let Some(load) = &step.load {
                load.append(&mut detail, labels, &detail_indent);
            }
            if step.read_context_changed {
                detail.push_str(&format!(
                    "\n{detail_indent}egraph read-equality context changed"
                ));
            }
            append_read_equalities(&mut detail, &step.read_equalities, labels, &detail_indent);
            if step.load.is_some() && step.read_equalities.is_empty() {
                detail.push_str(&format!(
                    "\n{detail_indent}no checked read equalities admitted by this step"
                ));
            }
            for forgotten in &step.forgotten_cells {
                let [cell, store] = [
                    (&forgotten.spelled[0], &forgotten.cell),
                    (&forgotten.spelled[1], &forgotten.store),
                ]
                .map(|(spelled, pointer)| match spelled {
                    Some(spelled) => format!("`{spelled}`"),
                    None => render::render_cell_address(pointer, labels),
                });
                let fact = render::render_proposition_labeled(&forgotten.indices_differ, labels);
                detail.push_str(&format!(
                    "\n{detail_indent}{}",
                    trace_text(
                        &format!(
                            "forgets cached {cell} beside the store to {store}: the store keeps it only on the stated fact {fact}"
                        ),
                        480
                    )
                ));
            }
            for walk in &step.history_stops {
                detail.push_str(&format!(
                    "\n{detail_indent}{}",
                    trace_text(
                        &format!(
                            "read history stopped after crossing {} recorded transition{} (a read follows at most one): {}",
                            walk.crossed,
                            if walk.crossed == 1 { "" } else { "s" },
                            render::render_transport_cell_walk(walk, labels)
                        ),
                        480
                    )
                ));
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
                None,
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
    if path.is_some_and(|path| {
        path.iter()
            .any(|index| *index >= super::proof::SYNTHETIC_SOURCE_INDEX_BASE)
    }) {
        return header.trim().split_once(": ").map_or_else(
            || "implicit contract step".to_owned(),
            |(_, description)| format!("implicit contract step: {description}"),
        );
    }
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

fn append_read_equalities(
    output: &mut String,
    equalities: &[TraceFact],
    labels: &mut MemoryStateLabels,
    indent: &str,
) {
    let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
    for equality in equalities {
        output.push_str(&format!(
            "\n{indent}admitted read equality: {}",
            render::render_proposition_labeled(&equality.kernel, labels)
        ));
    }
}

fn append_added_facts(
    output: &mut String,
    facts: &[TraceFact],
    labels: &mut MemoryStateLabels,
    indent: &str,
) {
    let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
    for fact in facts {
        if !visible_checked_fact(&fact.kernel) {
            continue;
        }
        output.push_str(&format!(
            "\n{indent}adds: {}",
            render::render_proposition_labeled(&fact.kernel, labels)
        ));
    }
}

pub(super) fn append_legend(trace: &mut String, labels: &mut MemoryStateLabels) {
    let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
    let legend = labels.trace_legend();
    if legend.is_empty() {
        return;
    }
    trace.push_str(&legend);
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

    #[test]
    fn a_recorded_node_keeps_its_address_after_the_candidate_is_dropped() {
        with_proof_trace("f", || {
            let payload = Arc::new(());
            let node = Arc::new(payload.clone());
            let key = trace_node_key(&node);
            assert_eq!(trace_node_key(&node), key);
            assert_eq!(Arc::weak_count(&node), 1);
            drop(node);
            assert_eq!(Arc::strong_count(&payload), 1);
            CAPTURE.with(|capture| {
                let capture = capture.borrow();
                let reservation = capture.as_ref().unwrap().node_keys[&key]
                    .downcast_ref::<std::sync::Weak<Arc<()>>>()
                    .unwrap();
                assert_eq!(reservation.as_ptr() as usize, key);
                assert!(reservation.upgrade().is_none());
            });
        });
    }

    use crate::kernel::{Address, AddressBase, AddressOffset, MachineTerm, SymbolicMemory};

    #[test]
    fn admitted_read_equalities_share_the_fact_printer_and_read_labels() {
        let address = Address::symbolic(crate::kernel::Variable(303_000));
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let read = Address::loaded_value(&memory, &address);
        let target = Address::function("callback");
        let fact = TraceFact {
            kernel: Proposition::condition_is(ConditionTerm::address_equal(read, target), true),
        };
        let mut labels = MemoryStateLabels::default();
        let mut ordinary = String::new();
        append_added_facts(
            &mut ordinary,
            &[TraceFact {
                kernel: fact.kernel.clone(),
            }],
            &mut labels,
            "  ",
        );
        let mut admitted = String::new();
        append_read_equalities(&mut admitted, &[fact], &mut labels, "  ");
        assert_eq!(
            admitted,
            ordinary.replace("adds:", "admitted read equality:")
        );
        let mut report = format!("{ordinary}{admitted}");
        append_legend(&mut report, &mut labels);
        assert!(report.contains("pointer read at state#1"), "{report}");
        assert!(report.contains("function `callback`"), "{report}");
    }

    #[test]
    fn legend_preserves_long_trace_and_line_boundaries() {
        let mut labels = MemoryStateLabels::default();
        labels.pointer_value_name(&Address::null());
        let mut text = "é".repeat(64 * 1024);
        text.push_str("\nfailed child argument comparison\nrequired: value#1");
        let original = text.clone();
        append_legend(&mut text, &mut labels);
        assert!(text.starts_with(&original));
        assert!(text.contains("label definitions"));
    }

    // Identical source spellings must not hide distinct reads, and the
    // refusal must reuse the same value labels as the preceding facts.
    #[test]
    fn child_comparison_keeps_read_values_distinct_from_source_spelling() {
        let address = Address::symbolic(crate::kernel::Variable(700_001));
        let first = crate::kernel::intern_memory(SymbolicMemory::new());
        let second = crate::kernel::intern_memory(SymbolicMemory::new().store(
            address.clone(),
            crate::kernel::ProgramValue::Int32(MachineTerm::constant(1)),
        ));
        let a = Address::loaded_value(&first, &address);
        let b = Address::loaded_value(&second, &address);
        let rid = Address::symbolic(crate::kernel::Variable(700_002));
        let facts = [a.clone(), b.clone()].map(|value| TraceFact {
            kernel: Proposition::condition_is(
                ConditionTerm::address_equal(value, rid.clone()),
                true,
            ),
        });
        let mut labels = MemoryStateLabels::default();
        // A proof-local name must not hide the read's defining state.
        labels.immutable_pointer_name(&a, "saved");
        let mut report = String::new();
        append_added_facts(&mut report, &facts, &mut labels, "  ");
        assert!(report.contains("adds: value#1 = value#2"), "{report}");
        assert!(report.contains("adds: value#3 = value#2"), "{report}");
        append_legend(&mut report, &mut labels);
        assert!(report.contains("state#1"), "{report}");
        assert!(report.contains("state#2"), "{report}");
        let comparison = ChildArgumentTrace {
            child: "sibling".into(),
            index: 0,
            actual: rid,
            required: b,
            related: vec![a],
            views: HashMap::new(),
        }
        .render(&mut labels);
        assert!(comparison.contains("supplied: value#2"), "{comparison}");
        assert!(
            comparison.contains("required: pointer_read(address value#4, memory state#2)"),
            "{comparison}"
        );
        assert!(
            comparison.contains("value#2 = value#1 is true"),
            "{comparison}"
        );
        assert!(comparison.contains("potentially relevant"));
        assert!(comparison.contains("different states alone do not establish unequal values"));
        assert!(!comparison.contains("Missing:"));
        let comparison = ChildArgumentTrace {
            child: "λ".repeat(64 * 1024),
            index: 0,
            actual: Address::null(),
            required: Address::null(),
            related: vec![],
            views: HashMap::new(),
        };
        let mut long = "λ".repeat(64 * 1024);
        let original = long.clone();
        comparison.append_to(&mut long, &mut labels);
        assert!(long.starts_with(&original));
        assert!(long.contains("failed child argument comparison"));
        assert!(long.contains("0 (null pointer)"));
    }

    #[test]
    fn trace_header_uses_resolved_source_tactic_location() {
        let label = |path: &[usize]| {
            (path == [3, 1]).then(|| ("tactic@475".to_owned(), SourcePosition::new(475, 1)))
        };
        assert_eq!(
            trace_header(
                "tactic 9223372036854775808: step",
                Some(&[super::super::proof::SYNTHETIC_SOURCE_INDEX_BASE + 1]),
                &label,
            ),
            "implicit contract step: step"
        );
        assert_eq!(
            trace_header(
                "tactic 3 > have body tactic 1: close()",
                Some(&[3, 1]),
                &label,
            ),
            "tactic@475: close()"
        );
    }

    #[test]
    fn facts_requirements_and_goals_share_read_identity_display() {
        use crate::kernel::{LoadKind, ProgramValue, Variable};
        use crate::surface::proof_diagnostics::{
            ProofDiagnosticOrigin, ProofFailureDiagnostic, render_terminal_message,
            render_trace_context_labeled,
        };
        struct State(Proposition);
        impl ProofDiagnosticState for State {
            fn kernel_goal(&self) -> Option<&Proposition> {
                Some(&self.0)
            }
            fn failed_requirement(&self) -> Option<(&str, &Proposition)> {
                Some(("required", &self.0))
            }
            fn premises(&self, _: usize) -> Vec<&Proposition> {
                vec![&self.0]
            }
            fn premise_count(&self) -> usize {
                1
            }
        }
        let pointer = Address::symbolic(Variable(782001));
        let first = SymbolicMemory::new();
        let second = first.clone().store(
            pointer.clone(),
            ProgramValue::UInt64(MachineTerm::uint64_constant(9)),
        );
        let fact = |memory| {
            Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left: Box::new(crate::kernel::MachineTerm::read_named(
                        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
                        pointer.clone(),
                        LoadKind::Bits64,
                    )),
                    right: Box::new(MachineTerm::uint64_constant(3)),
                },
                true,
            )
        };
        let earlier = fact(first);
        let later = fact(second);
        let diagnostic = ProofFailureDiagnostic {
            failing_path: None,
            checks: None,
            origin: ProofDiagnosticOrigin {
                stage: crate::surface::proof_diagnostics::ProofDiagnosticStage::CheckedStep,
                location: "test".into(),
                source_tactic_path: None,
            },
            claim_label: "same_display".into(),
            reason: "missing".into(),
            state: Some(std::sync::Arc::new(State(earlier.clone()))),
        };
        let ordinary = render_terminal_message("missing", &diagnostic, &[]);
        let mut labels = MemoryStateLabels::default();
        let context = render_trace_context_labeled(&diagnostic, &[], &mut labels);
        let mut added = String::new();
        append_added_facts(
            &mut added,
            &[TraceFact { kernel: earlier }, TraceFact { kernel: later }],
            &mut labels,
            "",
        );
        let goal = context
            .lines()
            .find_map(|l| l.strip_prefix("goal: "))
            .unwrap();
        assert!(
            goal.contains("read<Bits64>(state#1, pointer=value#1)"),
            "{goal}"
        );
        // The ordinary report spells the same read in source terms, one
        // spelling for the goal, the requirement and the premise alike.
        let ordinary_goal = ordinary
            .lines()
            .find_map(|l| l.trim_start().strip_prefix("goal: "))
            .unwrap();
        assert!(!ordinary_goal.contains("state#"), "{ordinary}");
        assert!(
            ordinary.contains(&format!("required: {ordinary_goal}")),
            "{ordinary}"
        );
        assert!(
            ordinary.contains(&format!("\n    {ordinary_goal}")),
            "{ordinary}"
        );
        assert!(added.contains(&format!("adds: {goal}")), "{added}");
        assert!(
            added.contains("read<Bits64>(state#2, pointer=value#1)"),
            "{added}"
        );
        assert!(
            ordinary.contains("<state A> is the memory before the function runs"),
            "{ordinary}"
        );
    }

    fn loadable_at(memory: SymbolicMemory) -> Proposition {
        Proposition::MemoryLoadable {
            memory,
            base: Address {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::Constant(0),
            },
            bytes: (MachineTerm::constant(1)).into(),
            wide: false,
        }
    }

    #[test]
    fn trace_and_goal_share_state_labels_without_conflating_distinct_memories() {
        with_proof_trace("f", || {
            let first = SymbolicMemory::default();
            let second = SymbolicMemory::new().with_block("different", 1);
            record(
                1,
                TraceStep {
                    header: "\n    source tactic 0: step".into(),
                    source_tactic_path: None,
                    call_source: None,
                    facts: vec![
                        TraceFact {
                            kernel: loadable_at(first.clone()),
                        },
                        TraceFact {
                            kernel: loadable_at(second.clone()),
                        },
                    ],
                    more_facts: 0,
                    frontier: None,
                    load: None,
                    read_equalities: Vec::new(),
                    read_context_changed: false,
                    transport: Some([
                        TraceFact {
                            kernel: loadable_at(first.clone()),
                        },
                        TraceFact {
                            kernel: loadable_at(second.clone()),
                        },
                    ]),
                    resources: Vec::new(),
                    more_resources: 0,
                    origin: None,
                    chosen: None,
                    forgotten_cells: Vec::new(),
                    history_stops: Vec::new(),
                },
            );
            let mut labels = MemoryStateLabels::default();
            let goal =
                render::render_internal_proposition_labeled(&loadable_at(first), &mut labels);
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
                None,
            )
            .unwrap();
            assert!(goal.contains("state#1"), "{goal}");
            assert!(trace.matches("adds: viewable(").count() == 2, "{trace}");
            assert!(trace.contains("state#2"), "{trace}");
            assert!(
                trace.contains("checked transport source: viewable(memory=state#1"),
                "{trace}"
            );
            assert!(
                trace.contains("checked transport target: viewable(memory=state#2"),
                "{trace}"
            );
        });
    }

    #[test]
    fn trace_integer_observations_do_not_hide_unspelled_theorem_facts() {
        use crate::kernel::{IntegerTerm, MachineIntegerType, Variable};
        let fact = TraceFact {
            kernel: Proposition::condition_is(
                ConditionTerm::integer_equal(
                    IntegerTerm::from_machine(
                        MachineIntegerType::UInt32,
                        MachineTerm::Variable(Variable(981_702)),
                    )
                    .unwrap(),
                    IntegerTerm::constant_i64(17),
                ),
                true,
            ),
        };
        let mut output = String::new();
        append_added_facts(
            &mut output,
            &[fact],
            &mut MemoryStateLabels::default(),
            "  ",
        );
        assert!(output.contains("adds:"), "{output}");
        assert!(!output.contains("no exact Click spelling"), "{output}");
        assert!(output.len() < 1024, "{output}");
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
            };
            record(1, step("\n    source tactic 0: step".into()));
            record(3, step("\n    have body tactic 0: normalize".into()));
            register_scope(
                2,
                deferred_lineage(|| {
                    vec![TracePathNode {
                        node: 1,
                        selected_arm: None,
                    }]
                }),
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
                &mut MemoryStateLabels::default(),
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
                None,
            )
            .unwrap();
            assert!(trace.contains("source tactic 0: step"), "{trace}");
            assert!(trace.contains("have body tactic 0: normalize"), "{trace}");
        });
    }

    #[test]
    fn trace_omits_generated_load_binding_beside_surface_branch_fact() {
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let pointer = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        };
        let variable =
            crate::kernel::load_variable_for_term(&crate::kernel::MachineTerm::read_named(
                crate::kernel::ProgramPoint::at(&memory),
                pointer.clone(),
                crate::kernel::LoadKind::Int32,
            ))
            .unwrap()
            .0;
        let defining = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(variable)),
                right: Box::new(crate::kernel::MachineTerm::read_named(
                    crate::kernel::ProgramPoint::at(&memory),
                    pointer,
                    crate::kernel::LoadKind::Int32,
                )),
            },
            true,
        );
        let mut output = String::new();
        append_added_facts(
            &mut output,
            &[
                TraceFact {
                    kernel: Proposition::condition_is(ConditionTerm::Constant(true), true),
                },
                TraceFact { kernel: defining },
            ],
            &mut MemoryStateLabels::default(),
            "  ",
        );
        assert_eq!(output, "\n  adds: true");
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
            };
            record(2, step("then step"));
            record(3, step("else step"));
            record(4, step("discarded candidate"));
            record_branch(
                1,
                TraceBranch {
                    header: "source tactic 0: branch".into(),
                    source_tactic_path: Some(vec![0]),
                    arm_names: ["then", "else"],
                    arms: [
                        (
                            BranchId::ROOT,
                            vec![TraceFact {
                                kernel: Proposition::condition_is(
                                    ConditionTerm::Constant(true),
                                    true,
                                ),
                            }],
                        ),
                        (
                            BranchId::ROOT,
                            vec![TraceFact {
                                kernel: Proposition::condition_is(
                                    ConditionTerm::Constant(false),
                                    true,
                                ),
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
                        kernel: Proposition::condition_is(ConditionTerm::Constant(true), true),
                    }],
                    more_facts: 0,
                    continuation_arm: None,
                    arm_paths: None,
                    _retained: Box::new(()),
                },
            );
            let trace = render(
                "f",
                &[TracePathNode {
                    node: 5,
                    selected_arm: None,
                }],
                &mut MemoryStateLabels::default(),
                &|_| Some(("tactic@1".into(), SourcePosition::new(1, 1))),
                &|_, _| Some(0),
                &|_, _| false,
                Some(&SourcePosition::new(2, 1)),
                None,
            )
            .unwrap();
            assert!(trace.contains("tactic@1: branch (then arm)"), "{trace}");
            assert!(trace.contains("adds: true"), "{trace}");
            assert!(trace.contains("then step"), "{trace}");
            assert!(!trace.contains("adds: false"), "{trace}");
            assert!(!trace.contains("else step"), "{trace}");
            assert!(!trace.contains("discarded candidate"), "{trace}");
            let summary = render(
                "f",
                &[TracePathNode {
                    node: 5,
                    selected_arm: None,
                }],
                &mut MemoryStateLabels::default(),
                &|_| Some(("tactic@1".into(), SourcePosition::new(1, 1))),
                &|_, _| None,
                &|_, _| false,
                Some(&SourcePosition::new(3, 1)),
                None,
            )
            .unwrap();
            assert!(summary.contains("adds: true"), "{summary}");
            assert!(!summary.contains("then step"), "{summary}");
            assert!(!summary.contains("else step"), "{summary}");
        });
    }

    #[test]
    fn completed_have_shows_only_its_exported_fact_unless_target_is_inside() {
        with_proof_trace("f", || {
            let fact = Proposition::condition_is(ConditionTerm::Constant(true), true);
            record(
                1,
                TraceStep {
                    header: "source tactic 2: have x == x".into(),
                    source_tactic_path: Some(vec![2]),
                    call_source: None,
                    facts: vec![TraceFact { kernel: fact }],
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
            record(
                2,
                TraceStep {
                    header: "have body tactic 1: normalize()".into(),
                    source_tactic_path: Some(vec![2, 1]),
                    call_source: None,
                    facts: Vec::new(),
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
                &mut MemoryStateLabels::default(),
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
                None,
            )
            .unwrap();
            assert!(report.contains("source tactic 2: have x == x"), "{report}");
            assert!(report.contains("adds: true"), "{report}");
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
                &mut MemoryStateLabels::default(),
                &|path| match path {
                    [2] => Some(("tactic@2".into(), SourcePosition::new(2, 1))),
                    [2, 1] => Some(("tactic@3".into(), SourcePosition::new(3, 1))),
                    _ => None,
                },
                &|_, _| None,
                &|path, _| path == [2],
                Some(&SourcePosition::new(3, 1)),
                None,
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
            };
            record(
                1,
                TraceStep {
                    source_tactic_path: Some(vec![0]),
                    facts: vec![TraceFact {
                        kernel: Proposition::condition_is(
                            ConditionTerm::address_equal(
                                Address::loaded_value(
                                    &crate::kernel::intern_memory(SymbolicMemory::new()),
                                    &Address::null(),
                                ),
                                Address::null(),
                            ),
                            true,
                        ),
                    }],
                    ..step("source tactic 0: accepted".into())
                },
            );
            record(
                2,
                TraceStep {
                    source_tactic_path: Some(vec![0]),
                    ..step("source tactic 0: abandoned candidate".into())
                },
            );
            record(3, step("source tactic 0: mark".into()));
            record_accepted_path(
                "f.contract",
                0,
                false,
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
                None,
            );
            let report = crate::surface::accepted_proof_trace(
                &|_, _| None,
                &|_, _, _| None,
                &|_, _, _| false,
                None,
            )
            .unwrap();
            assert!(report.contains("accepted"), "{report}");
            assert!(report.contains("label definitions"), "{report}");
            assert!(report.contains("value#1 ="), "{report}");
            assert!(report.contains("state#1 ="), "{report}");
            assert!(report.contains("initial empty memory"), "{report}");
            assert!(!report.contains("abandoned candidate"), "{report}");
            assert!(!report.contains(": mark"), "{report}");
            let targeted = render(
                "f.contract",
                &[TracePathNode {
                    node: 3,
                    selected_arm: None,
                }],
                &mut MemoryStateLabels::default(),
                &|_| Some(("tactic@2".into(), SourcePosition::new(2, 1))),
                &|_, _| None,
                &|_, _| false,
                Some(&SourcePosition::new(2, 1)),
                None,
            )
            .unwrap();
            assert!(targeted.contains("accepted"), "{targeted}");
            assert!(!targeted.contains("abandoned candidate"), "{targeted}");
            record(
                4,
                TraceStep {
                    source_tactic_path: Some(vec![1]),
                    ..step("source tactic 1: unfinished arm".into())
                },
            );
            record_unfinished_path(
                "f.contract",
                0,
                vec![TracePathNode {
                    node: 4,
                    selected_arm: None,
                }],
                Box::new(()),
                None,
            );
            let locate = |path: &[usize]| {
                let line = path[0] + 2;
                Some((format!("tactic@{line}"), SourcePosition::new(line, 1)))
            };
            let target = SourcePosition::new(3, 1);
            assert!(
                render_accepted(
                    &mut MemoryStateLabels::default(),
                    &|_, path| locate(path),
                    &|_, _, _| None,
                    &|_, _, _| false,
                    Some(&target),
                )
                .is_none(),
                "an unfinished arm cannot become an accepted proof trace"
            );
            let unfinished = render(
                "f.contract",
                &[],
                &mut MemoryStateLabels::default(),
                &locate,
                &|_, _| None,
                &|_, _| false,
                Some(&target),
                None,
            )
            .unwrap();
            assert!(unfinished.contains("unfinished arm"), "{unfinished}");
            assert!(!unfinished.contains("abandoned candidate"), "{unfinished}");
            record_certification_failure_path(
                "f.contract",
                0,
                vec![TracePathNode {
                    node: 4,
                    selected_arm: None,
                }],
                Box::new(()),
                None,
            );
            let mut shared_labels = MemoryStateLabels::default();
            let rejected_address = Address::symbolic(crate::kernel::Variable(987_771));
            shared_labels.immutable_pointer_name(&rejected_address, "rejected_fact_address");
            shared_labels.pointer_value_name(&rejected_address);
            let failed_prefix = render_accepted(
                &mut shared_labels,
                &|_, path| locate(path),
                &|_, _, _| None,
                &|_, _, _| false,
                Some(&target),
            )
            .expect("a certification refusal retains the written checked prefix");
            assert!(
                failed_prefix.contains("checked prefix; certification failed"),
                "{failed_prefix}"
            );
            assert!(failed_prefix.contains("unfinished arm"), "{failed_prefix}");
            assert!(
                !failed_prefix.contains("abandoned candidate"),
                "{failed_prefix}"
            );
            assert!(!failed_prefix.contains("accepted path"), "{failed_prefix}");
            assert!(
                shared_labels
                    .trace_legend()
                    .contains("rejected_fact_address")
            );
        });
    }
}
