use super::prelude::*;

#[cfg(test)]
thread_local! {
    static CONDITION_IMPLICATION_ANTECEDENT_CHECKS: Cell<usize> = const { Cell::new(0) };
}
use std::cell::{Cell, RefCell};

mod condition_reasoning;
mod memory_reasoning;
mod proposition_reasoning;

// Global equality resolution can re-enter itself through snapshot and alias
// facts. Two levels retain the framed symbolic-load cases while making failed
// searches terminate conservatively instead of overflowing the stack.
const MEMORY_LOAD_EQUALITY_DEPTH_LIMIT: usize = 2;
const SIGNED_INTERVAL_DEPTH_LIMIT: usize = 32;

thread_local! {
    static MEMORY_LOAD_EQUALITY_DEPTH: Cell<usize> = const { Cell::new(0) };
}

struct MemoryLoadEqualityDepthGuard;

impl MemoryLoadEqualityDepthGuard {
    fn enter() -> Option<Self> {
        MEMORY_LOAD_EQUALITY_DEPTH.with(|depth| {
            let current = depth.get();
            if current >= MEMORY_LOAD_EQUALITY_DEPTH_LIMIT {
                note_search_truncation();
                return None;
            }
            depth.set(current + 1);
            Some(Self)
        })
    }
}

impl Drop for MemoryLoadEqualityDepthGuard {
    fn drop(&mut self) {
        MEMORY_LOAD_EQUALITY_DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
}

/// How a structural walk compares two load atoms. The walk itself is exact —
/// it only ever descends through matching constructors — so the whole
/// relation is only as strong as the load-atom rule plugged in here.
type LoadAtomsMatch<'a> = &'a dyn Fn(&Bitvector32Term, &Bitvector32Term) -> bool;

fn pointers_equal_with_load_atoms(
    left: &Pointer,
    right: &Pointer,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    left.block == right.block
        && offsets_equal_with_load_atoms(&left.offset, &right.offset, loads_match)
}

fn offsets_equal_with_load_atoms(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    match (left, right) {
        (PointerOffsetTerm::Add(ll, lr), PointerOffsetTerm::Add(rl, rr)) => {
            offsets_equal_with_load_atoms(ll, rl, loads_match)
                && offsets_equal_with_load_atoms(lr, rr, loads_match)
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && terms_equal_with_load_atoms(left_value, right_value, loads_match)
        }
        _ => left == right,
    }
}

fn terms_equal_with_load_atoms(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    match (left, right) {
        (Bitvector32Term::MemoryLoad(_, _), Bitvector32Term::MemoryLoad(_, _)) => {
            loads_match(left, right)
        }
        (Bitvector32Term::Add(ll, lr), Bitvector32Term::Add(rl, rr))
        | (Bitvector32Term::Subtract(ll, lr), Bitvector32Term::Subtract(rl, rr))
        | (Bitvector32Term::Multiply(ll, lr), Bitvector32Term::Multiply(rl, rr)) => {
            terms_equal_with_load_atoms(ll, rl, loads_match)
                && terms_equal_with_load_atoms(lr, rr, loads_match)
        }
        _ => left == right,
    }
}

/// Exact structural condition equality with load atoms compared by
/// `loads_match`. Only matching constructors recurse and everything else
/// falls back to `==`, so two structurally different conditions never match
/// however permissive `loads_match` is.
fn conditions_equal_with_load_atoms(
    left: &ConditionTerm,
    right: &ConditionTerm,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    if left == right {
        return true;
    }
    let terms = |ll, rl, lr, rr| {
        terms_equal_with_load_atoms(ll, rl, loads_match)
            && terms_equal_with_load_atoms(lr, rr, loads_match)
    };
    match (left, right) {
        (
            ConditionTerm::Bitvector32SignedLessThan(ll, lr),
            ConditionTerm::Bitvector32SignedLessThan(rl, rr),
        )
        | (
            ConditionTerm::Bitvector32SignedLessEqual(ll, lr),
            ConditionTerm::Bitvector32SignedLessEqual(rl, rr),
        )
        | (
            ConditionTerm::Bitvector32SignedGreaterThan(ll, lr),
            ConditionTerm::Bitvector32SignedGreaterThan(rl, rr),
        )
        | (
            ConditionTerm::Bitvector32SignedGreaterEqual(ll, lr),
            ConditionTerm::Bitvector32SignedGreaterEqual(rl, rr),
        )
        | (ConditionTerm::Bitvector32Equal(ll, lr), ConditionTerm::Bitvector32Equal(rl, rr))
        | (
            ConditionTerm::Bitvector32SignedAddOverflows(ll, lr),
            ConditionTerm::Bitvector32SignedAddOverflows(rl, rr),
        )
        | (
            ConditionTerm::Bitvector32SignedSubtractOverflows(ll, lr),
            ConditionTerm::Bitvector32SignedSubtractOverflows(rl, rr),
        )
        | (
            ConditionTerm::Bitvector32SignedMultiplyOverflows(ll, lr),
            ConditionTerm::Bitvector32SignedMultiplyOverflows(rl, rr),
        )
        | (
            ConditionTerm::Bitvector32SignedDivideOverflows(ll, lr),
            ConditionTerm::Bitvector32SignedDivideOverflows(rl, rr),
        )
        | (
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(ll, lr),
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(rl, rr),
        ) => terms(ll, rl, lr, rr),
        (ConditionTerm::PointerOffsetEqual(ll, lr), ConditionTerm::PointerOffsetEqual(rl, rr)) => {
            offsets_equal_with_load_atoms(ll, rl, loads_match)
                && offsets_equal_with_load_atoms(lr, rr, loads_match)
        }
        (ConditionTerm::PointerEqual(ll, lr), ConditionTerm::PointerEqual(rl, rr)) => {
            pointers_equal_with_load_atoms(ll, rl, loads_match)
                && pointers_equal_with_load_atoms(lr, rr, loads_match)
        }
        _ => false,
    }
}

/// Compares two load atoms by their pointers alone, ignoring which memory
/// snapshot each carries.
///
/// NOT sound as an equality on its own: two loads of one pointer in
/// different snapshots hold different values whenever a write between the
/// snapshots reached that pointer. It exists only as a cheap prefilter that
/// discards hopeless candidates before a proving comparison runs, and every
/// caller must decide the surviving pairs with a real check.
fn load_atoms_equal_ignoring_memories(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    match (left, right) {
        (
            Bitvector32Term::MemoryLoad(_, left_pointer),
            Bitvector32Term::MemoryLoad(_, right_pointer),
        ) => pointers_equal_ignoring_memories(left_pointer, right_pointer),
        _ => left == right,
    }
}

/// Structural pointer equality that treats two loads of one location as
/// equal regardless of which memory snapshot each spelling carries. Cheap:
/// no proving, no canonicalization.
pub(crate) fn pointers_equal_ignoring_memories(left: &Pointer, right: &Pointer) -> bool {
    pointers_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
}

/// Cheap, assumption-free necessary condition for
/// [`Assumptions::conditions_equal_modulo_proven_snapshots`]: same structure,
/// with load atoms compared by pointer only.
///
/// Snapshot-blind, so it is NOT an equivalence and must never decide fact
/// availability on its own — it only narrows the candidate set before the
/// proving comparison runs.
pub fn conditions_equal_ignoring_memories(left: &ConditionTerm, right: &ConditionTerm) -> bool {
    conditions_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
}

pub(super) fn resources_equal_ignoring_memories(left: &CResource, right: &CResource) -> bool {
    let values_match = |left: &CValue, right: &CValue| match (left, right) {
        (CValue::Int32(left), CValue::Int32(right))
        | (CValue::UInt8(left), CValue::UInt8(right)) => {
            terms_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            pointers_equal_ignoring_memories(left, right)
        }
        _ => false,
    };
    match (left, right) {
        (CResource::Memory(left), CResource::Memory(right)) => {
            terms_equal_with_load_atoms(
                left.start(),
                right.start(),
                &load_atoms_equal_ignoring_memories,
            ) && terms_equal_with_load_atoms(
                left.end(),
                right.end(),
                &load_atoms_equal_ignoring_memories,
            ) && pointers_equal_ignoring_memories(left.base(), right.base())
        }
        (
            CResource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        )
        | (
            CResource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Token {
                name: right_name,
                arguments: right_arguments,
            },
        ) => {
            left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments)
                    .all(|(left, right)| values_match(left, right))
        }
        _ => false,
    }
}

fn equality_graph_terms_match(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    if left == right {
        return true;
    }
    let (
        Bitvector32Term::MemoryLoad(left_memory, left_pointer),
        Bitvector32Term::MemoryLoad(right_memory, right_pointer),
    ) = (left, right)
    else {
        return false;
    };
    left_pointer == right_pointer
        && (left_memory == right_memory
            || super::reasoning::canonical_memory_for_shared_pointer_load(
                left_memory,
                left_pointer,
            ) == super::reasoning::canonical_memory_for_shared_pointer_load(
                right_memory,
                right_pointer,
            ))
}

thread_local! {
    static SIMP_REASONING_FUEL: Cell<Option<usize>> = const { Cell::new(None) };
    static SIMP_FACT_REASONING_DEPTH: Cell<usize> = const { Cell::new(0) };
    static ATOMIC_PREMISE_MINIMIZATION_DEPTH: Cell<usize> = const { Cell::new(0) };
    static CONDITION_DECISIONS_IN_PROGRESS: RefCell<BTreeSet<ConditionTerm>> =
        const { RefCell::new(BTreeSet::new()) };
}

struct AtomicPremiseMinimizationGuard;

impl AtomicPremiseMinimizationGuard {
    fn disable() -> Self {
        ATOMIC_PREMISE_MINIMIZATION_DEPTH.with(|depth| depth.set(depth.get() + 1));
        Self
    }
}

impl Drop for AtomicPremiseMinimizationGuard {
    fn drop(&mut self) {
        ATOMIC_PREMISE_MINIMIZATION_DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
}

fn atomic_premise_minimization_disabled() -> bool {
    ATOMIC_PREMISE_MINIMIZATION_DEPTH.with(|depth| depth.get() != 0)
}

/// True while any condition decision is in progress on this thread. Deep
/// reasoning helpers use this to avoid re-entering `decide` from inside a
/// decision, which would cycle through order-fact matching and memory-load
/// resolution.
pub(super) fn inside_condition_decision() -> bool {
    CONDITION_DECISIONS_IN_PROGRESS.with(|in_progress| !in_progress.borrow().is_empty())
}

thread_local! {
    static SEARCH_TRUNCATIONS: Cell<u64> = const { Cell::new(0) };
    static DECIDE_MEMO: RefCell<std::collections::HashMap<(u64, ConditionTerm), Option<bool>>> =
        RefCell::new(std::collections::HashMap::new());
    static ASSUMPTIONS_MEMO_IDS: RefCell<std::collections::HashMap<Assumptions, u64>> =
        RefCell::new(std::collections::HashMap::new());
    static NEXT_ASSUMPTIONS_MEMO_ID: Cell<u64> = const { Cell::new(0) };
    static EQUAL_FROM_FACTS_MEMO: RefCell<
        std::collections::HashMap<(u64, Bitvector32Term, Bitvector32Term), bool>,
    > = RefCell::new(std::collections::HashMap::new());
    static TRANSPORT_EQUAL_MEMO: RefCell<
        std::collections::HashMap<(u64, Bitvector32Term, Bitvector32Term), bool>,
    > = RefCell::new(std::collections::HashMap::new());
    static CONSTANT_NORMALIZATION_MEMO: RefCell<
        std::collections::HashMap<(u64, Bitvector32Term), Option<i64>>,
    > = RefCell::new(std::collections::HashMap::new());
    static ATOMIC_DERIVATION_MEMO: RefCell<
        std::collections::HashMap<(u64, bool), std::collections::HashMap<Proposition, bool>>,
    > = RefCell::new(std::collections::HashMap::new());
}

// The memo tables are bounded so a long verification cannot grow them without
// limit. Ids are drawn from a never-reset counter, so clearing the intern
// table cannot alias an old id to different contents.
const ASSUMPTIONS_MEMO_ID_LIMIT: usize = 20_000;
const DECIDE_MEMO_LIMIT: usize = 500_000;
const CONSTANT_NORMALIZATION_SEARCH_LIMIT: usize = 32;

/// Content-derived memo identity: equal fact sets share an id, and any
/// in-place mutation changes the contents and therefore the id, so a decision
/// memoized under an id can never be replayed against different facts.
fn assumptions_memo_id(assumptions: &Assumptions) -> u64 {
    ASSUMPTIONS_MEMO_IDS.with(|ids| {
        let mut ids = ids.borrow_mut();
        if let Some(id) = ids.get(assumptions) {
            return *id;
        }
        if ids.len() >= ASSUMPTIONS_MEMO_ID_LIMIT {
            ids.clear();
        }
        let id = NEXT_ASSUMPTIONS_MEMO_ID.with(|next| {
            let id = next.get();
            next.set(id + 1);
            id
        });
        ids.insert(assumptions.clone(), id);
        id
    })
}

/// Memo identity for the DAG-walk memo tables in api.rs: the ambient scope's
/// id when one is live (no hashing), the content-derived id otherwise.
/// `None` when memoization is disabled, so `CLICK_DISABLE_DECIDE_MEMO`
/// bypasses those tables too.
pub(super) fn dag_memo_assumptions_id(assumptions: &Assumptions) -> Option<u64> {
    if decide_memo_disabled() {
        return None;
    }
    Some(
        ambient_assumptions_memo_id(assumptions)
            .unwrap_or_else(|| assumptions_memo_id(assumptions)),
    )
}

thread_local! {
    static ASSUMPTIONS_ID_SCOPES: RefCell<Vec<(usize, u64)>> = const { RefCell::new(Vec::new()) };
}

/// Resolves the memo id for a fact set that is borrowed for the duration of
/// the returned guard, skipping the content hash when an enclosing scope
/// already resolved the same object.
///
/// The address comparison is sound because every recorded scope belongs to a
/// live borrow further up the stack: while such a borrow is alive its object
/// cannot be dropped, so an equal address is the same object with the same
/// contents.
pub(crate) struct AssumptionsIdScope {
    id: u64,
    pushed: bool,
}

impl AssumptionsIdScope {
    pub(crate) fn enter(assumptions: &Assumptions) -> Self {
        if let Some(id) = ambient_assumptions_memo_id(assumptions) {
            return Self { id, pushed: false };
        }
        let address = assumptions as *const Assumptions as usize;
        let id = assumptions_memo_id(assumptions);
        ASSUMPTIONS_ID_SCOPES.with(|scopes| scopes.borrow_mut().push((address, id)));
        Self { id, pushed: true }
    }
}

/// The memo id for this fact set if an enclosing [`AssumptionsIdScope`]
/// already resolved this same object, with no content hashing. Interior
/// reasoning helpers use this so only designated entry points ever pay the
/// hash; outside any scope they simply run unmemoized, as before memoization
/// existed.
fn ambient_assumptions_memo_id(assumptions: &Assumptions) -> Option<u64> {
    let address = assumptions as *const Assumptions as usize;
    ASSUMPTIONS_ID_SCOPES.with(|scopes| {
        scopes
            .borrow()
            .iter()
            .rev()
            .find(|(scope_address, _)| *scope_address == address)
            .map(|(_, id)| *id)
    })
}

impl Drop for AssumptionsIdScope {
    fn drop(&mut self) {
        if self.pushed {
            ASSUMPTIONS_ID_SCOPES.with(|scopes| {
                scopes.borrow_mut().pop();
            });
        }
    }
}

/// True when CLICK_DISABLE_DECIDE_MEMO is set: decision and equality-graph
/// memoization is bypassed so behavior can be compared against the
/// unmemoized prover. Checked once per thread.
fn decide_memo_disabled() -> bool {
    thread_local! {
        static DISABLED: std::cell::OnceCell<bool> = const { std::cell::OnceCell::new() };
    }
    DISABLED.with(|disabled| {
        *disabled.get_or_init(|| std::env::var_os("CLICK_DISABLE_DECIDE_MEMO").is_some())
    })
}

/// Records that a reasoning search was cut short by ambient thread-local
/// state (a fuel budget, a recursion-depth guard, or an in-progress-decision
/// cycle cut) rather than by the query itself. `decide` results computed
/// under such a cut are path-dependent, so the decision memo must not cache
/// a `None` whose search was truncated.
pub(super) fn note_search_truncation() {
    SEARCH_TRUNCATIONS.with(|count| count.set(count.get() + 1));
}

const DEFAULT_SIMP_REASONING_FUEL: usize = 300;
const MAX_SIMP_FACT_REASONING_DEPTH: usize = 8;

struct SimpReasoningFuelGuard {
    previous: Option<usize>,
}

impl SimpReasoningFuelGuard {
    fn enter() -> Self {
        SIMP_REASONING_FUEL.with(|fuel| {
            let previous = fuel.get();
            if previous.is_none() {
                fuel.set(Some(DEFAULT_SIMP_REASONING_FUEL));
            }
            Self { previous }
        })
    }
}

impl Drop for SimpReasoningFuelGuard {
    fn drop(&mut self) {
        SIMP_REASONING_FUEL.with(|fuel| fuel.set(self.previous));
    }
}

fn consume_simp_reasoning_fuel() -> bool {
    if crate::instrumentation::deadline_exceeded() {
        note_search_truncation();
        return false;
    }
    SIMP_REASONING_FUEL.with(|fuel| match fuel.get() {
        None => true,
        Some(0) => {
            note_search_truncation();
            false
        }
        Some(remaining) => {
            fuel.set(Some(remaining - 1));
            true
        }
    })
}

struct SimpFactReasoningDepthGuard;

impl SimpFactReasoningDepthGuard {
    fn enter() -> Option<Self> {
        SIMP_FACT_REASONING_DEPTH.with(|depth| {
            let current = depth.get();
            if current >= MAX_SIMP_FACT_REASONING_DEPTH {
                note_search_truncation();
                return None;
            }
            depth.set(current + 1);
            Some(Self)
        })
    }
}

impl Drop for SimpFactReasoningDepthGuard {
    fn drop(&mut self) {
        SIMP_FACT_REASONING_DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
}

struct ConditionDecisionGuard {
    condition: ConditionTerm,
}

impl ConditionDecisionGuard {
    // Order matching can compare memory loads, which can ask alias questions
    // whose pointer arithmetic re-enters the original order query. Repeating
    // an in-progress query cannot add evidence, so stop that branch
    // conservatively instead of recursing through the Rust stack.
    fn enter(condition: &ConditionTerm) -> Option<Self> {
        CONDITION_DECISIONS_IN_PROGRESS.with(|in_progress| {
            let mut in_progress = in_progress.borrow_mut();
            if !in_progress.insert(condition.clone()) {
                note_search_truncation();
                return None;
            }
            Some(Self {
                condition: condition.clone(),
            })
        })
    }
}

impl Drop for ConditionDecisionGuard {
    fn drop(&mut self) {
        CONDITION_DECISIONS_IN_PROGRESS.with(|in_progress| {
            in_progress.borrow_mut().remove(&self.condition);
        });
    }
}

fn bitvector_terms_equal_after_exact_materialization(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    fn normalize(term: &Bitvector32Term) -> Bitvector32Term {
        let mut current = term.clone();
        for _ in 0..64 {
            let Bitvector32Term::MemoryLoad(memory, pointer) = &current else {
                break;
            };
            let Some(CValue::Int32(value)) = memory.known_value(pointer) else {
                break;
            };
            if value == current {
                break;
            }
            current = value;
        }
        current
    }

    normalize(left) == normalize(right)
}

fn proposition_has_free_bitvector_variable(proposition: &Proposition, variable: Variable) -> bool {
    match proposition {
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            proposition_has_free_bitvector_variable(left, variable)
                || proposition_has_free_bitvector_variable(right, variable)
        }
        Proposition::Not(body) => proposition_has_free_bitvector_variable(body, variable),
        Proposition::ForAll { var, body, .. } | Proposition::Exists { var, body, .. } => {
            *var != variable && proposition_has_free_bitvector_variable(body, variable)
        }
        proposition => {
            let mut variables = BTreeSet::new();
            collect_proposition_bitvector_variables(proposition, &mut variables);
            variables.contains(&variable)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SignedConstantResolution {
    Unknown,
    Known(i64),
    Ambiguous,
}

impl SignedConstantResolution {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Ambiguous, _) | (_, Self::Ambiguous) => Self::Ambiguous,
            (Self::Unknown, resolution) | (resolution, Self::Unknown) => resolution,
            (Self::Known(left), Self::Known(right)) if left == right => Self::Known(left),
            (Self::Known(_), Self::Known(_)) => Self::Ambiguous,
        }
    }

    fn from_term(term: Bitvector32Term) -> Self {
        signed_bitvector_constant(&term).map_or(Self::Unknown, Self::Known)
    }

    fn map(self, operation: impl FnOnce(i64) -> Bitvector32Term) -> Self {
        match self {
            Self::Known(value) => Self::from_term(operation(value)),
            Self::Unknown => Self::Unknown,
            Self::Ambiguous => Self::Ambiguous,
        }
    }
}

#[cfg(test)]
impl Proposition {
    pub(super) fn peel_implications(&self) -> &Self {
        match self {
            Self::Implies(_, body) => body.peel_implications(),
            _ => self,
        }
    }
}

impl Assumptions {
    #[cfg(test)]
    pub(super) fn reset_condition_implication_antecedent_checks() {
        CONDITION_IMPLICATION_ANTECEDENT_CHECKS.with(|checks| checks.set(0));
    }

    #[cfg(test)]
    pub(super) fn condition_implication_antecedent_checks() -> usize {
        CONDITION_IMPLICATION_ANTECEDENT_CHECKS.with(Cell::get)
    }

    /// Keep repeated decisions over this borrowed fact set under one memo
    /// identity. Recursive memory resolution can ask several alias questions
    /// about the same large context; without an enclosing scope each question
    /// re-hashes the entire context before consulting the decision memo.
    pub(super) fn enter_id_scope(&self) -> AssumptionsIdScope {
        AssumptionsIdScope::enter(self)
    }

    pub fn new() -> Self {
        Self::default()
    }

    /// Removes separation propositions while preserving arithmetic, equality,
    /// and other contextual facts. Resource-definition projection uses this
    /// to detect ownership conflicts that a contradictory fact from the same
    /// definition must not conceal.
    pub(crate) fn without_explicit_separation_facts(mut self) -> Self {
        self.prop_facts.retain(|proposition| {
            !matches!(
                proposition,
                Proposition::CMemoryDisjoint { .. } | Proposition::CResourceSeparate { .. }
            )
        });
        self
    }

    /// Keep contextual loadability consequences as explicit proof obligations
    /// instead of silently discharging them while symbolic execution is being
    /// planned.
    ///
    /// Condition reasoning is unchanged: this flag only controls the
    /// obligation boundary used by the evaluator.
    pub(crate) fn defer_non_exact_loadability_obligations(mut self) -> Self {
        self.defer_non_exact_loadability_obligations = true;
        self
    }

    pub(crate) fn should_defer_non_exact_loadability_obligations(&self) -> bool {
        self.defer_non_exact_loadability_obligations
    }

    /// Surface-certificate synthesis uses this only to structurally lower a
    /// candidate spelling before comparing it with an already-certified
    /// kernel proposition. Ordinary proof checking must not enable it.
    pub(crate) fn allow_symbolic_contract_loads(mut self) -> Self {
        self.allow_symbolic_contract_loads = true;
        self
    }

    pub(crate) fn should_allow_symbolic_contract_loads(&self) -> bool {
        self.allow_symbolic_contract_loads
    }

    pub(crate) fn defer_non_exact_condition_reasoning(mut self) -> Self {
        self.defer_non_exact_condition_reasoning = true;
        self
    }

    pub(super) fn should_defer_non_exact_condition_reasoning(&self) -> bool {
        self.defer_non_exact_condition_reasoning
    }

    pub(crate) fn prefer_symbolic_external_loads(mut self) -> Self {
        self.prefer_symbolic_external_loads = true;
        self
    }

    pub(super) fn should_prefer_symbolic_external_loads(&self) -> bool {
        self.prefer_symbolic_external_loads
    }

    pub(crate) fn proves_exact(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.condition_facts.get(condition) == Some(value)
            }
            Proposition::And(left, right) => self.proves_exact(left) && self.proves_exact(right),
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.condition_facts.get(condition) == Some(&!*value)
                }
                _ => self.prop_facts.contains(proposition),
            },
            _ => self.prop_facts.contains(proposition),
        }
    }

    pub fn assume_condition(mut self, condition: ConditionTerm, value: bool) -> Self {
        if let ConditionTerm::Bitvector32Equal(left, right) = &condition
            && let Some((left, right)) = bitvector_equality_after_additive_cancellation(left, right)
        {
            self = self.assume_condition(ConditionTerm::equal(left, right), value);
        }
        if let ConditionTerm::PointerEqual(left, right) = &condition
            && left.block == right.block
        {
            self = self.assume_condition(
                ConditionTerm::pointer_offset_equal(left.offset.clone(), right.offset.clone()),
                value,
            );
        }
        self.condition_facts.insert(condition, value);
        self
    }

    pub fn assume_proposition(mut self, proposition: Proposition) -> Self {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self = self.assume_condition(condition, value);
            }
            Proposition::And(left, right) => {
                self = self.assume_proposition(*left);
                self = self.assume_proposition(*right);
            }
            Proposition::Not(body) => match *body {
                Proposition::ConditionIs(condition, value) => {
                    self = self.assume_condition(condition, !value);
                }
                body => {
                    self.prop_facts.insert(Proposition::Not(Box::new(body)));
                }
            },
            proposition => {
                self.prop_facts.insert(proposition);
            }
        }
        self
    }

    pub fn pure_facts(&self) -> Vec<Proposition> {
        let mut facts = self
            .condition_facts
            .iter()
            .map(|(condition, value)| Proposition::ConditionIs(condition.clone(), *value))
            .collect::<Vec<_>>();
        facts.extend(self.prop_facts.iter().cloned());
        facts
    }

    fn without_free_bitvector_variable(&self, variable: Variable) -> Self {
        let mut assumptions = self.clone();
        assumptions.condition_facts.retain(|condition, _| {
            let mut variables = BTreeSet::new();
            collect_condition_bitvector_variables(condition, &mut variables);
            !variables.contains(&variable)
        });
        assumptions
            .prop_facts
            .retain(|proposition| !proposition_has_free_bitvector_variable(proposition, variable));
        assumptions
    }

    pub(super) fn includes(&self, required: &Self) -> bool {
        required
            .condition_facts
            .iter()
            .all(|(condition, value)| self.condition_facts.get(condition) == Some(value))
            && required
                .prop_facts
                .iter()
                .all(|proposition| self.prop_facts.contains(proposition))
    }
}

fn proposition_derivation(
    conclusion: &Proposition,
    rule: PropositionDerivationRule,
) -> PropositionDerivation {
    PropositionDerivation {
        conclusion: conclusion.clone(),
        rule,
    }
}

impl PropositionDerivation {
    /// Check this proof tree against an available context without searching for
    /// alternate proofs.
    pub fn replay(&self, available: &Assumptions) -> bool {
        let id_scope = AssumptionsIdScope::enter(available);
        match &self.rule {
            PropositionDerivationRule::ContextFree => solve_builtin_prop(&self.conclusion),
            PropositionDerivationRule::ContextualAtomic {
                premises,
                premises_id,
                for_simp,
            } => {
                (id_scope.id == *premises_id || available.includes(premises))
                    && premises.replays_atomic_derivation(&self.conclusion, *for_simp, *premises_id)
            }
            PropositionDerivationRule::Explosion { premises } => {
                available.includes(premises) && premises.is_inconsistent()
            }
            PropositionDerivationRule::And { left, right } => {
                let Proposition::And(expected_left, expected_right) = &self.conclusion else {
                    return false;
                };
                left.conclusion == **expected_left
                    && right.conclusion == **expected_right
                    && left.replay(available)
                    && right.replay(available)
            }
            PropositionDerivationRule::OrLeft(proof) => {
                let Proposition::Or(expected, _) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **expected && proof.replay(available)
            }
            PropositionDerivationRule::OrRight(proof) => {
                let Proposition::Or(_, expected) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **expected && proof.replay(available)
            }
            PropositionDerivationRule::DoubleNegation(proof) => {
                let Proposition::Not(body) = &self.conclusion else {
                    return false;
                };
                let Proposition::Not(expected) = body.as_ref() else {
                    return false;
                };
                proof.conclusion == **expected && proof.replay(available)
            }
            PropositionDerivationRule::Implies { antecedent, body } => {
                let Proposition::Implies(expected_antecedent, expected_body) = &self.conclusion
                else {
                    return false;
                };
                antecedent == expected_antecedent.as_ref()
                    && body.conclusion == **expected_body
                    && body.replay(&available.clone().assume_proposition(antecedent.clone()))
            }
            PropositionDerivationRule::ImpliesFalseAntecedent(proof) => {
                let Proposition::Implies(expected_antecedent, _) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == Proposition::Not(Box::new(expected_antecedent.as_ref().clone()))
                    && proof.replay(available)
            }
            PropositionDerivationRule::ForAllBody(proof) => {
                let Proposition::ForAll { var, body, .. } = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **body
                    && proof.replay(&available.without_free_bitvector_variable(*var))
            }
            PropositionDerivationRule::FiniteForAll { instances } => {
                let expected = available.finite_forall_instantiations(&self.conclusion);
                !expected.is_empty()
                    && derivations_match_propositions(instances, &expected)
                    && instances.iter().all(|proof| proof.replay(available))
            }
            PropositionDerivationRule::FiniteContextSplit {
                variable,
                lower,
                upper,
                premises,
                instances,
            } => {
                if !available.includes(premises) {
                    return false;
                }
                let Some(range) = premises.finite_context_range(*variable) else {
                    return false;
                };
                if range.lower < *lower || range.upper > *upper {
                    return false;
                }
                let Ok(width) = usize::try_from(upper - lower + 1) else {
                    return false;
                };
                if width > FINITE_CONTEXT_SPLIT_LIMIT {
                    return false;
                }
                let expected = (*lower..=*upper)
                    .map(|value| {
                        substitute_bitvector_variable_in_proposition(
                            &self.conclusion,
                            *variable,
                            &signed_i64_bitvector_constant(value),
                        )
                    })
                    .collect::<Vec<_>>();
                derivations_match_propositions(instances, &expected)
                    && instances.iter().all(|proof| proof.replay(available))
            }
            PropositionDerivationRule::UpperBoundSplit {
                bound,
                variable,
                pivot,
                below,
                at,
            } => {
                if available.condition_facts.get(bound) != Some(&true)
                    || upper_bound_split_candidate(bound) != Some((*variable, pivot))
                {
                    return false;
                }
                let term = Bitvector32Term::Variable(*variable);
                below.conclusion == self.conclusion
                    && at.conclusion == self.conclusion
                    && below.replay(&available.clone().assume_condition(
                        ConditionTerm::signed_less_than(term.clone(), pivot.clone()),
                        true,
                    ))
                    && at.replay(
                        &available
                            .clone()
                            .assume_condition(ConditionTerm::equal(term, pivot.clone()), true),
                    )
            }
            PropositionDerivationRule::DisjunctionCases { disjunction, cases } => {
                if !matches!(self.conclusion, Proposition::Or(_, _))
                    || !available.prop_facts.contains(disjunction)
                {
                    return false;
                }
                let mut expected_cases = Vec::new();
                collect_or_cases(disjunction, &mut expected_cases);
                if expected_cases.len() < 2
                    || expected_cases.len() > DISJUNCTION_CASE_LIMIT
                    || cases.len() != expected_cases.len()
                {
                    return false;
                }
                let mut base = available.clone();
                base.prop_facts.remove(disjunction);
                cases.iter().zip(expected_cases).all(|(proof, case)| {
                    proof.conclusion == self.conclusion
                        && proof.replay(&base.clone().assume_proposition(case))
                })
            }
        }
    }
}

/// The `(variable, pivot)` an assumed condition licenses splitting on, when it
/// says `variable <= pivot` in either spelling. Shared by the search and the
/// replay so the two cannot drift.
fn upper_bound_split_candidate(condition: &ConditionTerm) -> Option<(Variable, &Bitvector32Term)> {
    let (left, right, plus_one) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => (left, right, true),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => (left, right, false),
        _ => return None,
    };
    let Bitvector32Term::Variable(variable) = left.as_ref() else {
        return None;
    };
    if !plus_one {
        return Some((*variable, right.as_ref()));
    }
    let Bitvector32Term::Add(pivot, one) = right.as_ref() else {
        return None;
    };
    (**one == Bitvector32Term::Constant(1)).then_some((*variable, pivot.as_ref()))
}

fn derivations_match_propositions(
    derivations: &[PropositionDerivation],
    propositions: &[Proposition],
) -> bool {
    derivations.len() == propositions.len()
        && derivations
            .iter()
            .zip(propositions)
            .all(|(derivation, proposition)| derivation.conclusion == *proposition)
}

fn relative_range_offset(value: &Bitvector32Term, origin: &Bitvector32Term) -> Bitvector32Term {
    match (value, origin) {
        (
            Bitvector32Term::Subtract(value, value_origin),
            Bitvector32Term::Subtract(origin, origin_origin),
        ) if value_origin == origin_origin => {
            Bitvector32Term::subtract(value.as_ref().clone(), origin.as_ref().clone())
        }
        _ => Bitvector32Term::subtract(value.clone(), origin.clone()),
    }
}

fn signed_int_min_term() -> Bitvector32Term {
    Bitvector32Term::Constant(i32::MIN as u32)
}

fn signed_int_max_term() -> Bitvector32Term {
    Bitvector32Term::Constant(i32::MAX as u32)
}

fn range_intervals_cover_target(target: &CMemoryRange, mut intervals: Vec<(i64, i64)>) -> bool {
    let Some(target_start) = signed_bitvector_constant(target.start()) else {
        return false;
    };
    let Some(target_end) = signed_bitvector_constant(target.end()) else {
        return false;
    };
    if target_end <= target_start {
        return true;
    }

    intervals.sort_unstable();
    let mut covered_until = target_start;
    for (start, end) in intervals {
        let start = start.max(target_start);
        let end = end.min(target_end);
        if end <= covered_until {
            continue;
        }
        if start > covered_until {
            return false;
        }
        covered_until = end;
        if covered_until >= target_end {
            return true;
        }
    }
    false
}

fn memory_range_length_term(range: &CMemoryRange) -> Bitvector32Term {
    match range.end() {
        Bitvector32Term::Add(base, length) if base.as_ref() == range.start() => {
            length.as_ref().clone()
        }
        Bitvector32Term::Add(length, base) if base.as_ref() == range.start() => {
            length.as_ref().clone()
        }
        end => Bitvector32Term::subtract(end.clone(), range.start().clone()),
    }
}

fn memory_range_shallowly_contained_in_parts(
    range: &CMemoryRange,
    base: &Pointer,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
) -> bool {
    memory_range_shallowly_contained(
        range,
        &CMemoryRange::new(base.clone(), start.clone(), end.clone()),
    )
}

fn memory_range_shallowly_contained(range: &CMemoryRange, parent: &CMemoryRange) -> bool {
    let Some(base_index) = range.base().element_index_from_base(parent.base()) else {
        return false;
    };
    let range_start = Bitvector32Term::add(base_index.clone(), range.start().clone());
    let range_end = Bitvector32Term::add(base_index, range.end().clone());
    affine_bitvector_difference_constant(&range_start, parent.start())
        .is_some_and(|delta| delta >= 0)
        && affine_bitvector_difference_constant(parent.end(), &range_end)
            .is_some_and(|delta| delta >= 0)
}

pub(super) fn memory_range_contained_for_memory_resolution(
    range: &CMemoryRange,
    parent: &CMemoryRange,
    assumptions: &Assumptions,
) -> bool {
    super::reasoning::with_memory_resolution_fuel(|| {
        memory_range_contained_for_memory_resolution_with_depth(range, parent, assumptions, 0)
    })
}

fn memory_range_contained_for_memory_resolution_with_depth(
    range: &CMemoryRange,
    parent: &CMemoryRange,
    assumptions: &Assumptions,
    depth: usize,
) -> bool {
    if memory_range_shallowly_contained(range, parent) {
        return true;
    }
    if depth > super::reasoning::MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT
        || !super::reasoning::consume_memory_resolution_fuel()
    {
        return false;
    }

    if super::reasoning::pointers_proven_equal_for_memory_resolution_with_depth(
        range.base(),
        parent.base(),
        assumptions,
        depth + 1,
    ) {
        return exact_less_equal_for_memory_resolution(parent.start(), range.start(), assumptions)
            && exact_less_equal_for_memory_resolution(range.end(), parent.end(), assumptions);
    }

    if affine_bitvector_difference_constant(range.end(), range.start()) == Some(1) {
        let pointer = range.base().offset_by_int32_elements(range.start().clone());
        if pointer_in_memory_range_for_memory_resolution_with_depth(
            &pointer,
            parent,
            assumptions,
            depth + 1,
        ) {
            return true;
        }
    }

    false
}

fn exact_less_equal_for_memory_resolution(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    if let (Some(left), Some(right)) = (
        signed_bitvector_constant(left),
        signed_bitvector_constant(right),
    ) {
        return left <= right;
    }
    if left == right
        || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        || assumptions.exact_condition_value(&ConditionTerm::signed_less_equal(
            left.clone(),
            right.clone(),
        )) == Some(true)
        || assumptions.has_exact_order_path(left, right, false)
    {
        return true;
    }
    if assumptions
        .condition_facts
        .iter()
        .any(|(condition, value)| {
            if !*value {
                return false;
            }
            let (fact_left, fact_right) = match condition {
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right)
                | ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right) => {
                    (fact_left.as_ref(), fact_right.as_ref())
                }
                _ => return false,
            };
            bitvector_terms_proven_equal_for_memory_resolution(fact_left, left, assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(
                    fact_right,
                    right,
                    assumptions,
                )
        })
    {
        return true;
    }
    let Some(left_constant) = signed_bitvector_constant(left) else {
        return false;
    };
    assumptions
        .condition_facts
        .iter()
        .any(|(condition, value)| {
            if !*value {
                return false;
            }
            let (fact_left, fact_right, strict) = match condition {
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right) => {
                    (fact_left.as_ref(), fact_right.as_ref(), false)
                }
                ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right) => {
                    (fact_left.as_ref(), fact_right.as_ref(), true)
                }
                _ => return false,
            };
            signed_bitvector_constant(fact_left)
                .is_some_and(|bound| left_constant <= if strict { bound + 1 } else { bound })
                && (fact_right == right
                    || bitvector_terms_proven_equal_for_memory_resolution(
                        fact_right,
                        right,
                        assumptions,
                    ))
        })
}

fn pointer_in_memory_range_shallow(pointer: &Pointer, range: &CMemoryRange) -> bool {
    pointer_in_range_shallow(pointer, range.base(), range.start(), range.end())
}

fn pointer_offsets_match_by_shallow_fact_graph(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            pointer_offsets_match_by_shallow_fact_graph(left_a, right_a, assumptions)
                && pointer_offsets_match_by_shallow_fact_graph(left_b, right_b, assumptions)
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right,
                byte_width: right_width,
            },
        ) => left_width == right_width && assumptions.bitvector_terms_equal_from_facts(left, right),
        _ => false,
    }
}

fn pointer_in_memory_range_for_memory_resolution_with_depth(
    pointer: &Pointer,
    range: &CMemoryRange,
    assumptions: &Assumptions,
    depth: usize,
) -> bool {
    pointer_in_range_for_memory_resolution_with_depth(
        pointer,
        range.base(),
        range.start(),
        range.end(),
        assumptions,
        depth,
    )
}

fn pointer_in_range_for_memory_resolution(
    pointer: &Pointer,
    base: &Pointer,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    super::reasoning::with_memory_resolution_fuel(|| {
        pointer_in_range_for_memory_resolution_with_depth(pointer, base, start, end, assumptions, 0)
    })
}

fn pointer_in_range_for_memory_resolution_with_depth(
    pointer: &Pointer,
    base: &Pointer,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    assumptions: &Assumptions,
    depth: usize,
) -> bool {
    if pointer.block != base.block
        || depth > super::reasoning::MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT
        || !super::reasoning::consume_memory_resolution_fuel()
    {
        return false;
    }
    let mut indexes = pointer
        .element_index_from_base(base)
        .into_iter()
        .collect::<Vec<_>>();
    if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
        if super::reasoning::pointer_offsets_equal_for_memory_resolution(
            left,
            &base.offset,
            assumptions,
            depth + 1,
        ) == Some(true)
            && let Some(index) = int32_element_index_from_offset(right)
            && !indexes.contains(&index)
        {
            indexes.push(index);
        }
        if super::reasoning::pointer_offsets_equal_for_memory_resolution(
            right,
            &base.offset,
            assumptions,
            depth + 1,
        ) == Some(true)
            && let Some(index) = int32_element_index_from_offset(left)
            && !indexes.contains(&index)
        {
            indexes.push(index);
        }
    }
    indexes
        .iter()
        .any(|index| bitvector_index_in_range_shallow(index, start, end, assumptions))
}

/// Pins a term to a signed constant using EXACT facts only: either the term
/// is itself constant, or one recorded exact equality names its value. Exact
/// condition facts are pinned verbatim into certificates, so both smart
/// execution and replay see the same set and the answer is deterministic.
/// One hop, no recursion: a value-dependent range endpoint like
/// `owner->len` is separated from its constant by exactly the recorded
/// resource fact, never by a rewrite chain.
fn exact_signed_constant(term: &Bitvector32Term, assumptions: &Assumptions) -> Option<i64> {
    if let Some(value) = signed_bitvector_constant(term) {
        return Some(value);
    }
    assumptions
        .condition_facts
        .iter()
        .find_map(|(condition, value)| {
            if !*value {
                return None;
            }
            let ConditionTerm::Bitvector32Equal(left, right) = condition else {
                return None;
            };
            if left.as_ref() == term {
                signed_bitvector_constant(right)
            } else if right.as_ref() == term {
                signed_bitvector_constant(left)
            } else {
                None
            }
        })
}

fn bitvector_index_in_range_shallow(
    index: &Bitvector32Term,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    if let (Some(index), Some(start), Some(end)) = (
        signed_bitvector_constant(index),
        signed_bitvector_constant(start),
        signed_bitvector_constant(end),
    ) {
        return start <= index && index < end;
    }
    // Value-dependent endpoints pinned by exact facts (e.g. a range end of
    // `owner->len` with the recorded exact fact `owner->len == 1`) resolve
    // to constants without any non-exact condition reasoning. Success only:
    // an unresolved or unsatisfied triple falls through to the other arms.
    if let (Some(index), Some(start), Some(end)) = (
        exact_signed_constant(index, assumptions),
        exact_signed_constant(start, assumptions),
        exact_signed_constant(end, assumptions),
    ) && start <= index
        && index < end
    {
        return true;
    }
    let lower_bound_is_exact = assumptions.exact_condition_value(
        &ConditionTerm::signed_less_equal(start.clone(), index.clone()),
    ) == Some(true)
        || assumptions.has_exact_order_path(start, index, false)
        || assumptions.should_defer_non_exact_condition_reasoning()
            && assumptions.has_order_path_for_memory_resolution(start, index, false)
        || start == &Bitvector32Term::Constant(0)
            && index.add_const_parts().is_some_and(|(base, increment)| {
                (increment as i32) > 0
                    && (assumptions.has_exact_order_path(start, &base, false)
                        || assumptions.should_defer_non_exact_condition_reasoning()
                            && assumptions
                                .has_order_path_for_memory_resolution(start, &base, false))
                    && (assumptions.exact_condition_value(&ConditionTerm::signed_add_overflows(
                        base.clone(),
                        Bitvector32Term::Constant(increment),
                    )) == Some(false)
                        || assumptions.exact_condition_value(&ConditionTerm::signed_add_overflows(
                            Bitvector32Term::Constant(increment),
                            base.clone(),
                        )) == Some(false)
                        // A recorded strict signed upper bound (`base < y`)
                        // pins `base < INT_MAX`, so `base + 1` cannot
                        // overflow. Exact facts only; extended-bridging
                        // scope only, to keep every other phase's range
                        // answers byte-identical to the pre-arc path.
                        || increment == 1
                            && super::api::extended_dag_bridging_active()
                            && assumptions.has_exact_strict_upper_bound(&base))
            });
    let upper_bound_is_exact = assumptions
        .exact_condition_value(&ConditionTerm::signed_less_than(index.clone(), end.clone()))
        == Some(true)
        || assumptions.has_exact_order_path(index, end, true)
        || assumptions.should_defer_non_exact_condition_reasoning()
            && assumptions.has_order_path_for_memory_resolution(index, end, true);
    if lower_bound_is_exact && upper_bound_is_exact {
        return true;
    }

    let Some(offset) = affine_bitvector_difference_constant(index, start) else {
        return false;
    };
    if offset < 0 {
        return false;
    }
    if let Some(length) = affine_bitvector_difference_constant(end, start) {
        return offset < length;
    }
    i32::try_from(offset).is_ok_and(|offset| {
        affine_bitvector_difference_atom(end, start).is_some_and(|length| {
            assumptions.has_exact_order_path(
                &Bitvector32Term::Constant(offset as u32),
                &length,
                true,
            ) || assumptions.should_defer_non_exact_condition_reasoning()
                && assumptions.has_order_path_for_memory_resolution(
                    &Bitvector32Term::Constant(offset as u32),
                    &length,
                    true,
                )
        })
    })
}

fn bitvector_index_outside_range_shallow(
    index: &Bitvector32Term,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    if let (Some(index), Some(start), Some(end)) = (
        signed_bitvector_constant(index),
        signed_bitvector_constant(start),
        signed_bitvector_constant(end),
    ) {
        return index < start || end <= index;
    }
    if assumptions.exact_condition_value(&ConditionTerm::signed_less_than(
        index.clone(),
        start.clone(),
    )) == Some(true)
        || assumptions.has_exact_order_path(index, start, true)
        || assumptions.exact_condition_value(&ConditionTerm::signed_less_equal(
            end.clone(),
            index.clone(),
        )) == Some(true)
        || assumptions.has_exact_order_path(end, index, false)
    {
        return true;
    }
    affine_bitvector_difference_constant(index, start).is_some_and(|offset| offset < 0)
        || affine_bitvector_difference_constant(index, end).is_some_and(|offset| 0 <= offset)
}

fn pointer_in_range_shallow(
    pointer: &Pointer,
    base: &Pointer,
    start: &Bitvector32Term,
    end: &Bitvector32Term,
) -> bool {
    let Some(index) = pointer.element_index_from_base(base) else {
        return false;
    };
    if let (Some(index), Some(start), Some(end)) = (
        signed_bitvector_constant(&index),
        signed_bitvector_constant(start),
        signed_bitvector_constant(end),
    ) {
        return start <= index && index < end;
    }

    let (Some(offset), Some(length)) = (
        affine_bitvector_difference_constant(&index, start),
        affine_bitvector_difference_constant(end, start),
    ) else {
        return false;
    };
    0 <= offset && offset < length
}

fn affine_bitvector_difference_constant(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<i64> {
    let mut terms = BTreeMap::new();
    let mut constant = 0i64;
    collect_affine_bitvector_terms(left, 1, &mut terms, &mut constant)?;
    collect_affine_bitvector_terms(right, -1, &mut terms, &mut constant)?;
    terms.retain(|_, coefficient| *coefficient != 0);
    terms.is_empty().then_some(constant)
}

fn affine_bitvector_difference_atom(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<Bitvector32Term> {
    let mut terms = BTreeMap::new();
    let mut constant = 0i64;
    collect_affine_bitvector_terms(left, 1, &mut terms, &mut constant)?;
    collect_affine_bitvector_terms(right, -1, &mut terms, &mut constant)?;
    terms.retain(|_, coefficient| *coefficient != 0);
    if constant != 0 || terms.len() != 1 {
        return None;
    }
    let (term, coefficient) = terms.into_iter().next()?;
    (coefficient == 1).then_some(term)
}

fn collect_affine_bitvector_terms(
    term: &Bitvector32Term,
    coefficient: i64,
    terms: &mut BTreeMap<Bitvector32Term, i64>,
    constant: &mut i64,
) -> Option<()> {
    match term {
        Bitvector32Term::Constant(value) => {
            *constant = constant.checked_add(coefficient.checked_mul(i64::from(*value as i32))?)?;
        }
        Bitvector32Term::Add(left, right) => {
            collect_affine_bitvector_terms(left, coefficient, terms, constant)?;
            collect_affine_bitvector_terms(right, coefficient, terms, constant)?;
        }
        Bitvector32Term::Subtract(left, right) => {
            collect_affine_bitvector_terms(left, coefficient, terms, constant)?;
            collect_affine_bitvector_terms(right, coefficient.checked_neg()?, terms, constant)?;
        }
        atom => {
            let current = terms.entry(atom.clone()).or_default();
            *current = current.checked_add(coefficient)?;
        }
    }
    Some(())
}

impl ProofObligation {
    pub fn new(proposition: Proposition) -> Self {
        Self {
            proposition,
            context: None,
            assumable: true,
        }
    }

    pub fn verification_condition(proposition: Proposition) -> Self {
        Self {
            proposition,
            context: None,
            assumable: false,
        }
    }

    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    pub fn is_assumable(&self) -> bool {
        self.assumable
    }

    pub fn condition(condition: ConditionTerm, value: bool) -> Self {
        Self::new(Proposition::ConditionIs(condition, value))
    }

    pub fn memory_loadable(memory: CMemory, pointer: Pointer) -> Self {
        Self::memory_loadable_bytes(memory, pointer, 4)
    }

    pub fn memory_loadable_bytes(memory: CMemory, pointer: Pointer, byte_width: u32) -> Self {
        Self::new(Proposition::CMemoryLoadable {
            memory,
            base: pointer,
            bytes: Bitvector32Term::Constant(byte_width),
        })
    }

    pub fn memory_can_store(memory: CMemory, pointer: Pointer) -> Self {
        Self::memory_can_store_bytes(memory, pointer, 4)
    }

    pub fn memory_can_store_bytes(memory: CMemory, pointer: Pointer, byte_width: u32) -> Self {
        Self::new(Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        })
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    pub fn context(&self) -> Option<&str> {
        self.context.as_deref()
    }

    pub(super) fn map_proposition(self, f: impl FnOnce(Proposition) -> Proposition) -> Self {
        Self {
            proposition: f(self.proposition),
            context: self.context,
            assumable: self.assumable,
        }
    }
}

impl ExecutionPureFact {
    pub fn new(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: true,
            certified: false,
            certified_store: None,
        }
    }

    pub(super) fn internal(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: false,
            certified: false,
            certified_store: None,
        }
    }

    pub(super) fn certified(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: true,
            certified: true,
            certified_store: None,
        }
    }

    pub(super) fn certified_store(
        before: CMemory,
        after: CMemory,
        pointer: Pointer,
        value: CValue,
        authorized_range: Option<CMemoryRange>,
    ) -> Self {
        Self {
            proposition: Proposition::CMemoryMutatesOnly {
                before: before.clone(),
                after: after.clone(),
                pointers: vec![pointer.clone()],
            },
            public: false,
            certified: true,
            certified_store: Some(CertifiedMemoryStore {
                before,
                after,
                pointer,
                value,
                authorized_range,
            }),
        }
    }

    pub(super) fn into_certified(mut self) -> Self {
        self.certified = true;
        self
    }

    pub(crate) fn with_proposition(mut self, proposition: Proposition) -> Self {
        self.proposition = proposition;
        self
    }

    pub fn condition(condition: ConditionTerm, value: bool) -> Self {
        Self::new(Proposition::ConditionIs(condition, value))
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    pub(crate) fn is_public(&self) -> bool {
        self.public
    }

    pub(crate) fn is_certified(&self) -> bool {
        self.certified
    }

    pub(super) fn certified_store_data(&self) -> Option<&CertifiedMemoryStore> {
        self.certified_store.as_ref()
    }
}

impl SymbolicCExecution {
    pub fn paths(&self) -> &[SymbolicCExecutionPath] {
        &self.paths
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.limit
    }
}

impl SymbolicCExecutionPath {
    pub(crate) fn assumptions(&self) -> &Assumptions {
        &self.assumptions
    }

    pub fn facts(&self) -> &[ExecutionPureFact] {
        &self.facts
    }

    pub fn effect_facts(&self) -> &[ExecutionPureFact] {
        &self.effect_facts
    }

    pub fn execution_facts(&self) -> Vec<ExecutionPureFact> {
        let mut facts = self.facts.clone();
        for fact in &self.effect_facts {
            if !facts.contains(fact) {
                facts.push(fact.clone());
            }
        }
        facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    pub fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

impl CFunctionExecutionCandidates {
    pub fn state(&self) -> &CState {
        &self.state
    }

    pub fn function(&self) -> &CFunction {
        &self.function
    }

    pub fn arguments(&self) -> &[CExpression] {
        &self.arguments
    }

    pub fn paths(&self) -> &[CFunctionExecutionCandidate] {
        &self.paths
    }
}

impl CFunctionExecutionCandidate {
    pub fn outcome(&self) -> &CFunctionOutcome {
        &self.outcome
    }

    pub fn facts(&self) -> &[ExecutionPureFact] {
        &self.facts
    }

    pub fn effect_facts(&self) -> &[ExecutionPureFact] {
        &self.effect_facts
    }

    pub fn execution_facts(&self) -> Vec<ExecutionPureFact> {
        let mut facts = self.facts.clone();
        for fact in &self.effect_facts {
            if !facts.contains(fact) {
                facts.push(fact.clone());
            }
        }
        facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }
}

impl SymbolicCConditionEvaluation {
    pub fn paths(&self) -> &[SymbolicCConditionEvaluationPath] {
        &self.paths
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.limit
    }
}

impl SymbolicCConditionEvaluationPath {
    pub fn facts(&self) -> &[ExecutionPureFact] {
        &self.facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    pub fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

/// True when a term contains any memory load, at any depth.
fn bitvector_term_contains_load(term: &Bitvector32Term) -> bool {
    match term {
        Bitvector32Term::MemoryLoad(_, _) => true,
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => false,
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            bitvector_term_contains_load(left) || bitvector_term_contains_load(right)
        }
        Bitvector32Term::BitwiseNot(value) => bitvector_term_contains_load(value),
        Bitvector32Term::If {
            then_term,
            else_term,
            ..
        } => bitvector_term_contains_load(then_term) || bitvector_term_contains_load(else_term),
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            bitvector_term_contains_load(start)
                || bitvector_term_contains_load(end)
                || bitvector_term_contains_load(initial)
                || bitvector_term_contains_load(body)
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            arguments.iter().any(bitvector_term_contains_load)
        }
    }
}

/// Reentrancy-guarded load-equality resolution: the memory-resolution prover
/// can re-enter the atomic prover through condition decisions, so run it at
/// most once per call tree.
fn atomic_load_equality_resolves(
    assumptions: &Assumptions,
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    thread_local! {
        static LOAD_EQUALITY_RESOLUTION_ACTIVE: Cell<bool> = const { Cell::new(false) };
    }
    if LOAD_EQUALITY_RESOLUTION_ACTIVE.with(Cell::get) {
        return false;
    }
    const LOAD_EQUALITY_RESOLUTION_DEPTH_LIMIT: usize = 64;
    if super::api::bitvector_term_deeper_than(left, LOAD_EQUALITY_RESOLUTION_DEPTH_LIMIT)
        || super::api::bitvector_term_deeper_than(right, LOAD_EQUALITY_RESOLUTION_DEPTH_LIMIT)
    {
        return false;
    }
    LOAD_EQUALITY_RESOLUTION_ACTIVE.with(|active| active.set(true));
    let resolved = super::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
        left,
        right,
        assumptions,
    );
    LOAD_EQUALITY_RESOLUTION_ACTIVE.with(|active| active.set(false));
    resolved
}
