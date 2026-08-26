# Make `step()` a simple proof step

Subgoal of [Retire the parallel replay proof engine](replay-smell.md). It
replaces that issue's open "smart `execute` law" question: there is no law to
unify once `step()` has no premise list to choose.

## Violated invariant

A statement step is one concrete C transition: the kernel symbolically
executes the next statement in the current proof context and the proof
object retains the successor. Today that operation is written
`step() using { P; ... }`, and `P` is not a list of premises in the
logical sense. It is the *input* to the kernel's symbolic execution: the
facts the kernel is allowed to see. The successor state depends on `P` —
with more facts visible a store's frame is tighter, a call keeps more cells
named, a `return c` is decided instead of split — and adding an entry never
makes the step fail or its result weaker. The one list therefore serves
three roles at once: it justifies the statement's prerequisites, it selects
which memory-reading facts get a post-state copy (the `Selected` transport
policy carries exactly the listed ones), and it supplies the disjointness
evidence the memory model uses to decide which cells keep their names.

Consequences, all observed on the linear execution route this week:

- "The minimal premises that justify this step" is not well defined. A step
  with fewer entries is not wrong, only weaker, and whether weaker is
  sufficient is decided by later tactics. The linear selector's omissions
  surfaced as failures at the outcome `simp` and the function `frame`, never
  at the step (`expanded_read_step_keeps_named_range_separation_premises`,
  `examples/ring-buffer`, `mdtests/composite_resource_clone_separate_target.md`,
  `mdtests/modular_pointer_postcondition.md`).
- Every mechanism for choosing `P` is a search whose only oracle is running
  the kernel: the planner (`P` = everything, verbose, O(context) per
  statement), the indexed selector (`P` = definedness plus a few indexed
  facts, drops what later tactics need), and the two "run once with
  everything, name what the kernel used" variants prototyped on 2026-08-25
  (a second symbolic execution per statement, or reasoning-provenance
  capture during the retained one). All of them exist to reconstruct an
  input the kernel already has.
- The certificate vocabulary spells kernel inputs as Surface Click
  (`at(statement(n).entry, ...)`, `at(statement(n).exit, ...)`,
  two-anchor equalities, resource-body facts), so every step also needs a
  spelling for facts whose only origin is a composite's observation or a
  havocked cell. Most of the `surface_synthesis` growth exists for this.

## Design

`step()` executes the next statement with the whole proof context visible
to the kernel. It takes no premise list. It is a simple tactic: explicit
input (the statement, the context established by the source above it), one
deterministic checked transition, bounded work, retained in provenance.
`execute()` is the repetition of `step()` to function exit;
`execute_until(statement(N))` is its repetition to a statement. Their
expansion is a sequence of `step();` lines.

What survives a step automatically, with nothing carried:

- facts that read no memory, and facts stated at a fixed snapshot (`old`,
  `at(point, ...)`, requirements) — true at every point;
- resource facts (`separate`, `contains`, `loadable` over ranges) — unless
  the statement consumes or produces the resource;
- facts about cells the kernel proves disjoint from the statement's effect
  from the context — the cell keeps its epoch name, so the fact stays
  literally true; with the callee's `ensures x == old(x)` visible when a
  call's result is materialized, the kernel keeps the old name instead of
  minting a fresh one plus an equality (the ring-buffer planner route does
  this today).

Facts about cells the statement writes are correctly invalidated by the
cell's new name; the statement's own facts (the store, the callee's
`ensures`) say what is there now. Facts about cells the context cannot
prove untouched are also renamed, which is the honest answer. `transport`
remains the tool for that residual: the author adds the missing evidence
with `have` and moves the fact. `frame() using` and `transport(P, Q)
using` are unchanged; their premises are real rules' premises.

The glossary sentence "a simple tactic uses only the facts its surface form
selects" no longer holds for `step()`; it uses the context. A step's
meaning is "execute this statement here", and the context is fixed by the
source above it, so explicit scripts remain authoritative: a `have`
changes what a step sees, search cannot.

`step() using { P; ... }` is deleted at the end of the migration. During
it, the form parses with the meaning "check each `P` is available, then
`step()`", so the existing corpus keeps verifying; expansion stops
emitting it in the first chunk.

## Efficiency

The cost of "see everything" must be zero; only what the kernel looks up
may cost. The proof object already keeps the context this way:
`ProofFacts` is persistent and indexed, and its `PureFactContext` is
maintained incrementally (adding a fact copies logarithmic paths). The
planner's O(context) per statement, and the 12,026 persistent nodes
(bound 3,049) the provenance prototype allocated on
`smart_store_selection_uses_only_statement_name_indexes` at size 64, came
from materializing that context into a `Vec<Proposition>` for the
transition entry (`certified_statement_transitions` takes a slice) and from
attempting a frame check for every listed memory fact per store.

Two known per-step scans exist on master, both bounded by the function's
state and both to be made lazy or indexed, not worked around:

- a call's havoc (`with_call_memory_havoc`) tests every current cell for
  disjointness from the mutable ranges; the memory derivation DAG already
  records the havoc as an edge and resolves reads lazily;
- each step enumerates the resource context's observable facts
  (`observable_facts_assuming_valid`), and resource consumption's cost
  depends on the resource algebra's indexing (see
  `indexed-resource-algebra-avoids-pairwise-context-work.md`).

## Plan, in order, one green commit each

1. **Transition reads the context.** `certified_statement_transitions`
   (and the wrapper `execute_step_successors_from_execution_point`) take
   the proof object's incremental `PureFactContext` instead of a fact
   slice; the per-step fact transport of listed memory facts is removed
   (name stability from the DAG replaces it). Arbiter:
   `smart_store_selection_uses_only_statement_name_indexes` at its current
   bound, re-aimed at a full-context step; a deterministic scaling
   regression over context sizes for one `step()`.
2. **`step()` is the full-context simple step on the Proof.**
   `apply_execution_statement_step` executes with the context; the smart
   `step`/`execute` selectors (`try_indexed_statement_step_*`,
   `try_linear_execute*`, `apply_planned_smart_step`,
   `apply_planned_smart_execute`) reduce to repetition. Arbiters: the
   fallback examples (`linked-list`, `recursive-zero-list`,
   `owned-string`, `ring-buffer`), the four shapes above, and the
   effect-script canaries (no planning transitions).
3. **Expansion emits `step();`.** The reference table, the "expansion
   uses `step() using`" rule, and the canaries that pin selection output
   (`grouped_calls_keep_contract_transitions_on_proof`,
   `resource_example_pipelines_have_no_outcome_fallbacks`,
   `linear_execute_until_retains_its_checked_execution_proof`, and their
   kin) move to the new output; the corpus's `frame() using` lists that
   cite step-carried facts are re-expanded.
4. **Both drivers run the same trivial law.** The interpreter's `execute`
   arm and the flat driver call the same repetition; the routing gates
   (`grouped_flat_proof_supported`, the structural routing) and the
   planner's step construction delete, per the replay issue's phase 1.
5. **Delete `step() using`.** Parser, `SimpleProofStep::StepUsing`,
   `check_step_using_facts`, the `Selected` transport policy, the premise
   spelling machinery whose only consumer was step selection
   (`synthesize_surface_equality_across_points` and the recorded-point
   spellings stay only if the outcome `simp` still needs them), and the
   documentation rows.

## Intended regressions

- A bare `step()` on a context of n unrelated facts allocates persistent
  nodes bounded by the statement's footprint, not n (deterministic curve
  over several n).
- `execute(); frame(); simp();` on each of the four shapes above verifies
  through the checked linear route with no planning transition and
  expands to `step();` lines plus outcome closers.
- Removing a `have` a later `transport` depends on fails the transport,
  never a step; a step never fails for a missing premise, only for a
  prerequisite unprovable in context, with that diagnostic.
- After chunk 5, the source grammar has no `step() using` and no
  certificate names statement premises.

## Acceptance criteria

`step()` is a simple tactic in the reference table; `execute` and
`execute_until` are its repetitions; `step() using` is gone from grammar,
checker, expansion, docs, and corpus; the replay issue's "smart `execute`"
section is replaced by a pointer here; the scaling regression above is in
the gate.

## Progress

Chunks 1–3 landed together (2026-08-26). `certified_statement_transitions`
and `certified_condition_transitions` take the proof object's incremental
`PureFactContext`; every statement step on the Proof runs in the whole
context (`Contextual` prerequisites, no transport for a bare step); source
`step();` is the bare `SimpleProofStep::Step`, and the planner retains
`Step` for every statement except a step into a C `if`, which keeps the
condition it selected as `step() using { cond }` until the branch-entry
law is unified in chunk 4. Findings worth keeping:

- A proof `if` whose arms begin with steps no longer tells the drivers by
  shape whether it enters a C branch or splits the proof logically; only
  the frontier decides (`Proof::frontier_is_execution_branch`). The C
  condition anchored at a wrong statement entry is rejected as a mismatched
  checked branch; any other non-matching condition is a logical split.
- Loop preservation records the invariants' and the loop condition's
  Surface spellings at the body entry, so the loop-effect frame can cite
  `i < owner->len` when `owner->len` has no readable spelling inside the
  body (`composite_resource_vector_fill_loop_snapshot`).
- The point transport's duplicate assumption of the registry-resolved
  source form was a non-canonical creation once sources are spelled with
  load variables; the reachability walk did not need it
  (`input_cursor_creates_only_canonical_terms`).
- The interpreter's `execute` arm still tries the exact selector before
  the planner; chunk 4 makes both drivers the same repetition of `step()`.

Chunk 4, first commit (2026-08-26): the shape gates
(`grouped_flat_proof_supported`, `top_level_structural_proof_supported`
and their predicates) are deleted. Every claim is checked by the structural
driver, then the flat driver, then the compatibility interpreter; a driver
declines with `None`, and its errors stay terminal. `CLICK_DBG_FALLBACK=1`
counts what still reaches the interpreter: nothing in the examples
(quarantined `owned-vector` aside) or the mdtests (down from 53 once a bare step's failure, the
planner's failure, and a generated proof's failure became terminal on the
checked route with their own diagnostics — the negative tests' expected
messages come from the checked route now — the empty-execution-leaf
shape gate on the flat driver was deleted, `execute_until` shares one
planner law (`Proof::apply_planned_execute_until`) between the drivers,
and an execution tactic after exit or an outcome tactic before exit is a
terminal diagnostic; an outcome operation after exit inside an `open`
scope is deferred on the scope body; a bare step decides a C `if` the
context decides; and path-aligned certificates keep a case split whose
arms' bare steps coincide; an `assumption` on a proposition judgment
accepts a discharged implication's consequent and a restricted `simp`
falls back to direct closure; mid-execution `transport` shares one
premise law, `Proof::apply_planned_fact_transport`, between the drivers).
A `branch ensuring` with a returned arm checks the interface on the
continuing arm at its boundary and joins terminally
(`frontier_branch_return`). Gaps closed on the
way, all in the drivers or the kernel, no script changes:

- A bare `frame()` among post-exit outcome operations, or at a case-split
  arm's exit, is searched on the exit Proof and kept as an ordered
  deferral, so expansion prints it after the `fold`/`have` it follows.
- Outcome `frame using` premises accept facts available across the
  recorded effects, atomically derivable resource facts, and a lowering at
  a recorded program point (a resource body fact observed at a call's
  exit); an outcome `assumption` closes on a fact available across the
  recorded effects.
- Each statement step records a readable spelling for every fact it
  introduces (output-sized).
- The goal-equality rewrite closure (`simp` closing `1 == x` from
  `x == 1`) works for a judgment stated at an execution frontier, such as
  a `have ... by simp` inside an `open` scope, reading spellings from the
  execution's surface map (`object_retain_many`).
- The kernel's call-havoc edge freezes the fact context in force when it
  is recorded (`CMemoryDerivation::CallHavoc { context }`). The
  assumption-free naming walk crosses it for a pointer that context proves
  outside the mutable ranges by ownership, so a cell an earlier callee
  wrote keeps its name across a later call into a disjoint owned resource
  (`mdtests/call_havoc_keeps_names_by_ownership.md`,
  `detachable_buffer_pipeline`, `ring_buffer_pipeline`). The crossing is
  memoized per edge and pointer; without that memo the branch-shaped
  fixture did 22x the work.
- A terminal proof-`if` join keeps each case's outcome paths with their
  own resources, and kernel certification of a checked unit runs once per
  group of outcome paths with the same recorded proof-case decisions
  (`ExecutionBranchDecision::proof_case`), with that group's case facts
  lowered at function entry, as the interpreter certifies each case as its
  own context (`mdtests/terminal_case_split_certifies_each_case.md`,
  `list_destroy`, `item_destroy`).

- A post-exit proof `if` whose condition a return path does not decide
  forks that path, one copy per polarity, each carrying the case fact and
  a recorded proof-case decision (`Proof::split_outcome_paths_by_case`);
  the deferred `if` is then decided on every path and certification runs
  once per case (`mdtests/outcome_case_split_forks_undecided_paths.md`,
  `list_prepend`, `pool_init`). A bare `frame()` inside a deferred arm is
  the ambient function frame checked per path; a tactic nested in a
  deferred arm registers its expansion capture by tactic index
  (`DeferredTacticCapture::NESTED`).

- A `branch` whose then arm returns while the else arm continues runs the
  continuation inside the continuing arm to function exit and joins the
  arms terminally, as `execute()` already represents such a C `if`
  (`mdtests/branch_with_one_returning_arm.md`, `refcount_pipeline`). With
  an `ensuring` interface the shape still declines to the interpreter: an
  interface join needs both arms at the boundary
  (`mdtests/frontier_branch_return.md`).

### Unification progress (2026-08-26)

Landed on master (`96d0e40f`), each green through `scripts/check.sh`:

- The branch arm-advancing law is one core (`advance_checked_branch_arms`)
  shared by the `Proof` branch driver and the open-scope branch handler.
- The entire **expanded-execution walker family** is deleted (~300 lines);
  the recursive source walker subsumes it. One representation gone.
- Post-exit outcome tactics interleave with a following node (a
  post-execution `if`): they defer onto the exit Proof and the continuation
  runs after, via a shared `defer_post_exit_outcome_tactic`.
- A non-terminal execution-frontier `If` node (arms reach a shared
  continuation, e.g. a loop/nested-branch/scope in an arm) is driven through
  the branch core like a `Branch`, in both the top-level driver and the
  recursive region walker.

### Interpreter deletion: current failure set

Replacing both interpreter fallbacks in `claim_proofs.rs` with a terminal
`unsupported_proof_shape` error (the deletion) starts at **17** failing unit
tests. A near-complete attempt is stashed on this branch as
`interpreter-deletion-17to5` (based on current master, so it re-applies
cleanly). It drives the 17 down to **5** with these fixes, all worth
keeping:

- `smart_frame_miss_error`: a smart `frame` miss is terminal with the
  exit / effect-goal / no-candidate diagnostic (the four `try_smart_frame_at`
  decline sites and the scope site).
- Both drivers are split into a `_inner` body plus a thin wrapper that
  publishes the expansion capture on any non-decline result (retention *or*
  terminal error), so `expand` still records through a failing verify.
- The three `supports_checked_frame_using` frame guards are removed so a
  frame is always attempted (a genuine miss is now the terminal error
  above); this alone cleared ~8 expansion tests.
- `pre_exit_outcome_tactic_error` covers `simp` and `frame`, and the
  pre-exit-diagnostic check is reordered before the `!saw_structure`
  decline, so `by simp` at function entry gives "requires execution to
  reach function exit first".
- `frontier_is_execution_branch` accepts a *raw* source condition
  (`flag != 0`, not just the anchored `at(stmt.entry, ...)` form), so a
  source `if` at a C-`if` frontier routes through the branch core.
- `advance_focused_execution_arm` handles a `loop` inside a branch arm.

The remaining **5** are nested / recursive branches and
branch-with-continuation shapes where the branch core's arm advance still
declines. Their exact proof-tree shapes (from `CLICK_DBG_SHAPE`):

- `frontier_local_loop_verifies_at_a_branch_local_frontier` /
  `branch_count`: `Lin[step,step]->If{Lin[step,loop]|Lin[step,step]}->Lin[step,simp]`.
  Now routes into the branch core (raw-condition fix), but the core
  declines — an arm `SmartStep` (`try_indexed_execute_step`) or the
  loop-in-arm advance returns `None`.
- `recursive_zero_list_branch_frames` / `zero_list_sum`:
  `Lin[observe]->If{Lin[execute]->If{Lin[frame]|Lin[frame]}->Lin[simp] | Lin[execute,frame,simp]}`.
  A terminal outer proof-case-split whose then-arm contains a *nested*
  execution `if`.
- `smart_execute_retains_nested_terminal_c_branches` / `write_nested`:
  `Open{If{Lin[step]->If{...}|Lin[step,step,step]}->Lin[frame]}->Lin[have,assumption,assumption]`.
  A nested execution `if` inside an `open` scope.
- `branch_continuation_claims_retain_their_selected_outcome_step` /
  `joined_increment`: `Lin[step]->Br{Lin[step]|Lin[step]}->Lin[step,step,simp]`.
  An explicit `Br` with a non-Done continuation.
- `expanded_execute_and_frame_replay_after_resource_branch` /
  `vector_replace_if`:
  `Lin[step,step,step,have]->Br{Lin[step,have,have,have]|...}->Lin[execute,have,frame,simp]`.
  A `Br` whose arms carry mid-execution `have`s and reach a continuation
  that itself `execute`s.

The deletion finishes by closing these 5, then removing
`execute_internal_proof`, `replay_linear_tactics_*`, the planner
construction entries, and the `OrderedProofUnit::Replay` arm, in one green
commit.

## Record of the abandoned carry (2026-08-25)

Before this design was chosen, a "carry" was prototyped in the linear
selector: preview the transition with the whole context under
reasoning-provenance capture, name what the kernel used (plus the sources
and frame premises of every fact it transported), spell them (recorded
form, synthesis at recorded entry points, two-anchor form, the carried
form at the statement exit), and re-apply. It fixed the store shape and
`modular_pointer_postcondition`, needed two general repairs to get there
(the call havoc reporting the separation it consumed as provenance; the
outcome `frame using` accepting availability across recorded effects), and
still failed `ring-buffer` (a carried fact about a composite-owned cell
has no readable spelling at any point) and `clone_cursor` (eleven
resource-fact premises of the outcome derivation with no spelling) while
tripping the store-selection scaling canary. It is the search this issue
deletes; the patch is not kept. The two general repairs are worth
reconsidering only if something still needs them after chunk 2.
