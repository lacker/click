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
