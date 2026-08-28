# Name proof-object branches explicitly

## Summary

The proof object can contain several open semantic branches of one proof.
The implementation currently calls those branches goals:
`ProofGoals` stores them, `GoalId` identifies them, and `GoalContext` stores
the state local to one of them. That vocabulary obscures an important
distinction:

- an `if`, `cases`, execution split, or feasible function outcome creates
  branches of the same proof; while
- loop initialization, loop preservation, loop effects, and a nested `have`
  body are distinct proof obligations and should use separate `Proof` values
  or explicit subproofs.

This issue is an internal conceptual cleanup. It does not propose new Surface
Click syntax, different proof semantics, implicit tactic parallelism, or a
different loop rule.

## Violated invariant

The implementation vocabulary should make this model mechanically apparent:

> A `Proof` represents one proof obligation and owns zero or more open
> branches. Each open branch owns one current obligation and its branch-local
> state. Only an explicit checked split creates semantic branches; cloning a
> `Proof` for smart search creates candidates, not branches. A distinct
> obligation starts a distinct proof or subproof.

The current names violate that invariant in several concrete ways:

- `ProofGoals` is a persistent map whose multiple entries are created by
  branching operations, not a general bag of unrelated obligations.
- `GoalContext` contains path-local facts, unfolded predicates, and an
  execution snapshot, so it is branch state rather than general context.
- `GoalId` identifies a sibling created by a split and later consumed by a
  join.
- comments claim that a proof has at most one open goal even though split
  regressions immediately exercise two simultaneous sibling entries.
- `start_loop_effect_goal` creates a fresh root `Proof`, which is a separate
  proof rather than another entry in the parent proof's branch collection.
- “branch” is overloaded by the generic semantic concept, the Surface
  `branch` tactic, `ProofBranch`, and `SimpleProofStep::Branch` without names
  that distinguish them.

This makes it too easy to mistake case branching for a collection of unrelated
goals, to mistake speculative proof forks for semantic branches, or to model
loop phases as siblings inside one proof.

## Canonical vocabulary

Use these terms consistently in implementation comments, design documents,
and internal tests:

- **proof**: evidence for one obligation, possibly with several open branches;
- **branch**: one open semantic case or execution path inside that proof;
- **obligation**: what one branch currently has to establish;
- **branch state**: facts, proof-local unfolds, and any execution snapshot
  owned by one branch;
- **arm**: a syntactic side of `if`, `cases`, or Surface `branch`; an
  infeasible arm creates no branch;
- **split**: a checked structural operation replacing one branch with child
  branches;
- **join**: a checked structural operation consuming sibling branches and
  producing their common continuation branch;
- **leaf**: a branch that has reached a typed boundary, such as a loop back
  edge;
- **candidate** or **fork**: a speculative immutable `Proof` value used by
  smart search; it is not a semantic branch;
- **path**: a completed checked execution history or outcome, rather than an
  open branch; and
- **subproof**: a separate nested proof for a distinct obligation, such as a
  `have` body.

“Goal” remains appropriate in user-facing diagnostics for a proposition the
user is trying to prove. It should not name the internal collection of open
branches.

## Target representation

The intended internal shape is:

```rust
struct Proof<'a> {
    environment: Arc<ProofEnvironment<'a>>,
    state: Arc<ProofState>,
    node: Arc<ProofNode>,
    focused_branch: BranchId,
}

struct ProofState {
    open_branches: OpenBranches,
    // Other proof-wide or transition-output fields remain to be classified.
}

struct OpenBranch {
    obligation: Obligation,
    state: BranchState,
}

enum Obligation {
    Proposition(PropositionObligation),
    ExecutionFrontier(FrontierObligation),
    FunctionOutcome(OutcomeObligation),
}

struct BranchState {
    facts: ProofFacts,
    unfolded_predicates: PersistentOrderedSet<String>,
    execution: Option<Arc<ExecutionProofState>>,
}
```

The `OpenBranch` wrapper is important. Merely renaming `GoalContext` to
`Branch` would still conflate the state local to a branch with the obligation
that branch must prove. Extracting the wrapper also removes the repeated
`context` field from every current `Goal` variant and the variant-by-variant
reconstruction in `Goal::with_context`.

## Naming map

Apply the following internal names unless implementation experience exposes a
clear conflict:

| Current | Target |
| --- | --- |
| `ProofGoals` | `OpenBranches` |
| `GoalId` | `BranchId` |
| `GoalContext` | `BranchState` |
| `Goal` | `Obligation` inside `OpenBranch` |
| `PropositionGoal` | `PropositionObligation` |
| `FrontierGoal` | `FrontierObligation` |
| `OutcomeGoal` | `OutcomeObligation` |
| `focused` | `focused_branch` |
| `focused_goal()` | `focused_branch()` |
| `goals()` | `branches()` |
| `sole_goal_id()` | `sole_branch_id()` |
| `focus(id)` | `focus_branch(id)` |
| `discharge_at()` | `close_at()` |
| `with_context_at()` | `with_branch_state_at()` |
| `outcome_goal_for_path()` | `outcome_branch_for_path()` |
| `focus_function_outcomes()` | `split_function_outcomes()` |
| `start_loop_effect_goal()` | `start_loop_effect_proof()` |

`SplitId` can remain: it identifies the checked split instance whose children
a join is authorized to consume. Split-record fields named only `ids` should
become `arm_branches` or another role-specific branch name.

Consider renaming the existing shared `ProofContext` family to
`ProofEnvironment` after the branch model lands. Those values hold immutable
theorem, function, lowering, and diagnostic inputs shared by every branch;
“environment” distinguishes them from `BranchState`. This is a secondary
cleanup and must not obscure the core branch change.

## Surface `branch` collision

Surface syntax remains unchanged. Internally, reserve unqualified “branch”
for the generic open-proof concept and qualify the tactic-specific types:

- parsed `ProofBranch` should become `ExecutionBranchTactic`; and
- `SimpleProofStep::Branch` should become `ExecutionBranch`.

An `if`, `cases`, and an execution `branch` tactic all create semantic
branches, but they are distinct checked split operations. “Arm” should refer
to their written sides; “branch” should refer to the feasible proof state
created from an arm.

## Separate proofs and subproofs

Do not put distinct obligations into `OpenBranches` merely to make this model
uniform:

- loop initialization is one proof;
- each loop-preservation obligation is a proof, which may itself branch;
- each loop-effect obligation is a proof derived from a checked preservation
  leaf;
- a `have` body is a nested subproof whose established proposition rejoins
  its parent; and
- resource scopes remain scopes around proof branches, not additional
  obligations manufactured as sibling branches.

Function outcomes are different. `split_function_outcomes` is a branch
operation: it replaces one function-exit frontier branch with one feasible
branch per checked return path. The instantiated outcome obligation may differ
by result value and path state, but all remain branches of the same function
proof.

## Implementation order

Land this cleanup in independently green chunks:

1. Introduce `OpenBranch { obligation, state }`, `OpenBranches`, `BranchId`,
   and branch-focused accessors. Update the proof-object implementation and
   tests without changing checked operations, certificates, diagnostics, or
   asymptotic behavior.
2. Rename split/join records, function-outcome branch APIs, and internal
   comments to the canonical vocabulary. Qualify the Surface `branch`
   tactic's Rust types without changing its spelling.
3. Rename separate-proof APIs such as `start_loop_effect_proof`, then update
   `design/proof-object-api.md`, the proof-object internals documentation,
   glossary entries, and module-level comments.
4. Audit `ProofState::locals`, `added_facts`, and `checked_facts`. Record
   whether each is proof-wide, branch-local, or transition output. Move a
   field only when the ownership rule and a focused regression make the
   change mechanical. File a separate issue if this audit exposes a semantic
   bug rather than folding it into the naming refactor.
5. Consider splitting `splits_and_scopes.rs` into branching and scope modules,
   and renaming `outcomes_and_focus.rs` to `outcome_branches.rs`, after the
   type model makes the module boundary clear.

Do not perform blind repository-wide replacement: “goal” remains valid for
user-visible proposition goals, and “branch” already names several distinct
surface and certificate constructs.

## Intended regressions

Adapt the existing persistent split/join regression into one explicitly named
branch-model test. It should establish that:

1. a fresh proof has one root `BranchId`;
2. a checked `if` split retires that id and creates two sibling branches;
3. advancing the focused branch preserves the untouched sibling;
4. focusing and advancing the sibling stays in the same proof lineage;
5. joining the exact siblings closes both child branches and restores one
   continuation branch under the parent identity; and
6. a foreign split record cannot join numerically colliding branches.

Add a small separate-proof regression for a loop effect: deriving the effect
proof creates a fresh proof with one root branch and does not add a branch to
the preservation proof. Existing behavior and certificate assertions should
remain unchanged.

Keep the deterministic branch scaling regression. Splitting, focusing,
updating, and joining must remain logarithmic in unrelated open branches plus
work proportional to the affected branch and its certificate delta. The
cleanup must not clone the complete branch map or every sibling state.

## Acceptance criteria

- `Proof` is documented and implemented as one proof with open branches.
- `OpenBranch` explicitly separates `Obligation` from `BranchState`.
- The proof-object implementation and its design documentation no longer use
  `ProofGoals`, `GoalId`, or `GoalContext` for this branch substrate.
- Split, focus, join, outcome, and preservation code consistently distinguish
  branches, arms, paths, candidates, leaves, and separate proofs.
- Loop phases and `have` bodies remain separate proofs or subproofs; they are
  not inserted as unrelated entries in `OpenBranches`.
- Surface Click syntax and semantics are unchanged, including `if`, `cases`,
  `branch`, loops, and resource scopes.
- Certificates and expansion output are unchanged except for internal Rust
  variant names that do not affect rendering.
- Existing branch identity, transactionality, expansion, and deterministic
  scaling regressions remain green, with the focused regressions above added
  or renamed.
- `scripts/check.sh` exits successfully.
- This issue file and its `issues/README.md` entry are deleted when the
  implementation, regressions, and documentation land.

## Non-goals

- applying one tactic implicitly to every branch;
- changing `step`, `execute`, loop, or resource semantics;
- combining loop phases into one proof;
- changing the existing C verification boundary;
- changing smart-tactic search completeness; or
- replacing persistent maps with a representation that weakens the verified
  scaling contract.
