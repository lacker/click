# Scaling

Priority: P2. Moved from P1 by user direction (2026-10-20): the remaining
causes cost verification time, not correctness, and do not block the rbtree
claim.

Soundness: not soundness. This is verifier performance. Every derivation the
steps below perform is kernel-checked today; the problem is that their work
grows with state the step does not touch, so a function with N objects costs
O(N²) to verify. It looks fine at small N and then exhausts budgets.

## Goal

Stamp out every quadratic scaling problem we can find in simple checking.
The contract is in [Verification Efficiency](../docs/internals/verification-efficiency.md):
a simple step's work is bounded by its selected operation, its explicit
inputs, indexed lookups and the proof-state delta, up to logarithmic factors.
A step that scans the whole state, re-derives something from the whole state,
or walks a collection that grows with the proof's history violates it, even
when each scan is cheap.

Fix the underlying representation rather than adding a cache or a skip in
front of a scan that stays linear. A fix is done when a deterministic
regression over several sizes shows the step flat.

## Reproduction

`scripts/step-scaling-hunt.py` generates one C function per shape and size,
with one explicit `step()` per statement, and prints each step's work.

```sh
cargo build --profile profiling --bin click
python3 scripts/step-scaling-hunt.py heap_objects --sizes 4,16,64,256
```

`heap_objects` creates, fills and releases N heap objects:

```c
int32 caller() {
    struct box* p0; ... struct box* pN;
    p0 = make_box(); p0->v = 0;      /* extern: produces boxed(result) */
    ...
    drop_box(p0); ...                /* extern: consumes boxed(p) */
    return 0;
}
```

with `resource boxed(p: struct box*) { owns *p; }`, each object unfolded for
its store and folded again.

On master `a826da1c` at N = 64: `pi = make_box()` is flat at 1,586 units;
`pi->v = i` grows from 1,049 to 1,977; `drop_box(pi)` charges 14,984 for the
first release (63 others live) falling to 1,400 for the last. The whole
proof charges 695,291 units at N = 64 and 13,933,163 at N = 256, with a
largest step of 69,033.

## Known causes

Each is the same pattern: a step recomputes something from the whole state
instead of from what the step changed.

1. **Fixed: a store through an unresolved pointer visited every cached
   cell**, including the slot of every earlier local, which no pointer value
   can reach. The cell store now keeps the pointer-reachable cell keys
   (`CellStore::pointer_reachable_cells`), caught up by diffing, and a store
   through a `Symbolic` pointer visits only those. `heap_objects` stores now
   cost 135 units at every position at N = 64.
2. **Composition evidence is a list that only grows.** Every step states
   about four states of the whole resource context as
   `Proposition::CResourceComposition` facts. Stores no longer read them:
   the write path states the writer's current composition as the store owner
   (`PureFactContext::with_store_owner`), and `owned_store_footprint` and
   `owned_composition_store_separated_evidence` read it alone. That removed
   25 of the 29 units per earlier object a `heap_objects` store cost (cause 1
   was the rest), and no
   mdtest, example or unit test depended on the older compositions. Without
   a store owner, ownership separation and the same-block separation search
   now read only the compositions listed under the two objects' members
   (`CompositionMemberIndex`), each listed by what it holds beyond an
   earlier admitted composition; that held `heap_objects`' `unfold` tactics,
   which grew about 27 units per earlier object, flat. The set itself is a
   persistent set, so stating a composition no longer copies it. About
   twenty other `resource_compositions.iter()` sites, in load resolution and
   condition reasoning, still scan the whole set; each needs the same
   argument for which listed compositions can answer it. Filing a
   composition fact bounded its variables by walking every held fact
   (`proposition_syntax_execution_variable_ceiling`), about four whole
   contexts per step; the bound is now cached on each canonical fact-set
   node, so a context one insertion derives computes that path alone
   (`composition_ceiling_reads_the_cached_fact_set`; `heap_objects` at
   N = 128, 406 to 9 million instructions).
3. **A call rebuilds what the caller keeps.** `call_kept_ownership` expanded
   every kept composite at every call to list the memory the caller keeps.
   Fixed for composites whose definition is argument-direct, such as
   `boxed`: the call opens none of them, and the recorded kept memory opens
   only the composites a question's address can name
   (`CallKeptRanges::range_holding`). `heap_objects` now costs 1,401 units per
   `drop_box` at every position at N = 64, and the whole proof 204,585 units
   (was 695,291). Still per call: residual instances and composites whose
   bodies read memory, a condition or a witness are opened at every call, so
   a function holding many of those still pays for each.
4. **Evidence checking re-validated each step.** A statement theorem listed
   every fact of the context it executed under as a premise, and recording
   it looked each one up again in that same context, and built a set of the
   whole retained history for any premise it missed, uncharged. Fixed in
   part: a statement theorem lists only its own path facts and obligations
   (`statement_theorems_do_not_list_the_context_they_executed_under`), and
   recording a step checks the frontier and running state but walks no
   premises. Memory states and resource contexts also order by a cached
   content hash first, so the lookups that remain no longer walk shared
   entries (`ordering_states_of_one_path_does_not_walk_their_shared_entries`).
   Together, on `heap_objects`: 6.28 to 3.75 billion instructions at
   N = 64, and a mean step of 18.7 to 6.4 ms at N = 256. Still open, under
   the rule in `AGENTS.md` (construct valid proofs; never produce-then-check):
   condition/function theorem contexts and observation/rewrite producers need
   caller-specific reconciliation. The old repeated-step and instance/population
   fold claims are superseded by the retained-result preparation work at
   `c53645952`: step/fold completion no longer reruns a primitive, and selected
   constructor-count/history controls pass. See the
   [current lifecycle audit](smart-tactics.md#e1-and-q1-logical-steps-and-evidence-lifecycle-deferred-evidencegaps)
   for the remaining scope; those controls do not certify every evidence path.
   A walk that meets
   an already checked branch or proof-case join no longer walks its arms
   again, so a statement inside nested joins is walked once per join that
   directly holds it rather than once per enclosing join. That walk, which
   collects the arms' memory steps, reads each recorded event's result and
   re-checks no premise or rewrite; it takes no facts. Population-authority and lifetime-end checks during function completion
   require a separate current-caller audit; prepared fold completion does not
   establish their cost. A plain composite `fold` or `unfold` is recorded from its
   producer's result without re-expanding or comparing (2.84 billion
   instructions at N = 64; fold work at N = 256 137,981 to 22,782). A
   path's execution-fact stream answered membership by scanning: a stream
   that had been filtered or selected (each path's facts are) dropped its
   proposition index, so every context published onto it compared each new
   fact against every fact already held, memory states included. The
   stream's indexes now cover its context blocks and survive filtering
   (`membership_reads_no_context_block_of_a_growing_stream`); at N = 128 the
   membership lookups went from 492 to 6 million instructions. A plain
   composite `unfold` also renormalized the whole context it composed its
   body into; it now normalizes around the body alone
   (`ResourceContext::normalized_around_facts`;
   `unfolding_one_object_does_not_renormalize_every_held_object`), and at
   N = 128 whole-context normalization went from 738 to 60 million
   instructions.
5. **Fixed: satisfying a composite checked every held one of its shape.**
   `ResourceContext::satisfies_fact` tried entailment against every held
   `boxed(..)` when the required pointer was spelled differently, so each
   `heap_objects` fold cost 3 units per live object. It now reads the held
   composites whose pointer is related to the required one
   (`direct_match_candidates_for`), and folds are flat.
6. **Fixed: a load through an unresolved pointer rebuilt every cell it may
   alias.** `canonical_memory_for_pointer_load` is assumption-free, and a
   `Symbolic` block's alias candidates narrow nothing, so the canonical memory
   of a load through one heap object was rebuilt from every earlier object's
   cell and every local's slot, at every unfold. The cell store now keeps the
   pointer-reachable cells with their values, caught up by its own changes,
   and the projection starts from that map and filters only the `local:`
   cells and the load's own block; each `heap_objects` unfold is flat
   (141 units at every position at N = 24).
7. **Fixed: a call reserved every variable its assumptions mention.** To
   pick fresh identities, a verified call collected every variable of every
   assumption, including each variable every named state holds: per call
   the facts times the state's variables, so cubic in `objects_and_calls`
   (`collect_assumption_variables`, x50 from N = 32 to 128). A fact context
   now keeps an upper bound on the execution-range variables its facts
   mention (`ExecutionVariableCeiling`): filing a fact reads its syntax, a
   fact that names a state is taken whole once when an execution first
   asks, and executions allocate above the bound instead of reserving the
   facts' variables (`asking_after_every_fact_takes_each_state_fact_whole_once`).
   `objects_and_calls` at N = 128: 10.69 to 9.90 billion instructions.
   Separately, lowering a function's requirements bound every parameter
   into the entry state again for each requirement; the state is now built
   once per requirement list.
8. **Building a function's entry context is quadratic in its parameters.**
   Several entry passes lower each requirement or resource clause on its
   own and rebuild, per requirement, structures that span every parameter:
   the entry state with each parameter bound, the parameter value map, the
   array references. `objects_and_calls`' entry context grows x7 from
   N = 32 to 128. Fixed in part: the passes that lower one requirement at a
   time now share one lowering state, and a frame's locals are persistent
   maps, so binding a local copies a search path rather than every binding
   (`binding_a_local_copies_a_search_path_not_the_frame`); `objects_and_calls`
   at N = 128, 9.90 to 9.58 billion instructions. Also fixed: the entry's
   resource clauses are lowered over one shared parameter environment
   (`ClauseParameters`) instead of each rebuilding the parameter values and
   array references (`entry_resource_clauses_do_not_rebuild_every_parameter`:
   560, 8,384 and 131,840 units at 16, 64 and 256 parameters before; 80,
   320 and 1,280 after). Also fixed: the other entry passes looked up
   every parameter for each requirement: segment evaluation, memory clause
   lowering, requirement elaboration, and the returned-place and `ensures`
   checks. A function's entry and proof now carry one `ParameterIndex`, and
   these passes read only the parameters a segment, memory clause or
   requirement names (`entry_setup_is_linear_in_owned_parameters`).
   `objects_and_calls` at N = 128: 9.06 to 8.59 billion instructions, its
   entry context 1.33 to 0.90 billion. Also fixed: a proof issues a
   theorem per path and claim, and each claim and theorem cloned the
   function's contract and its specification's argument and requirement
   lists. Those are now shared (`Arc`), so a clone copies none of them
   (`cloned_functions_and_specifications_share_their_contracts`);
   `objects_and_calls` at N = 128, 8.59 to 8.17 billion instructions.
   Also fixed: building a proof's fact set reserved every variable its
   facts mention, and the entry states one loadability fact per object over
   the one entry memory holding every object, so each fact added that whole
   memory's variables again. A fact set now collects each interned memory's
   variables once (`collecting_each_memory_once`;
   `facts_over_one_memory_reserve_its_variables_once`: 6,083, 106,895 and
   2,141,373 units at 16, 64 and 256 facts before; 2,033, 8,993 and 46,803
   after). Against current master, the entry-only shape at N = 128 went
   from 3.66 to 3.52 billion instructions, and `objects_and_calls` from 9.13
   to 8.99 billion.
9. **Fixed: comparing equal resource contexts walked every fact.** A call
   that takes the caller's ownership and returns it rebuilds a context with
   the same facts in fresh storage. Contexts order by content hash first, so
   every equal pair fell through to a fact-by-fact walk: in
   `objects_and_calls` about 78 such walks per step at N = 128, each over
   every live object. A context now also keeps its facts as a canonical
   multiset (`canonical_fact_set.rs`), a hash-consed treap whose shape is a
   function of its contents, so equal contexts share one root and compare
   by pointer (`comparing_equal_resource_contexts_walks_no_facts`).
   Equality is now multiset equality rather than insertion order.
   `objects_and_calls` at N = 128: 9.58 to 9.04 billion instructions. Its
   charged step work is now flat (largest step 4,692 units at N = 16 to
   128) and mean step time grows x1.1 from N = 32 to 128.

The sequential-loop clause bug filed beside these is fixed; "Sequential loop
clauses" in
[verification-efficiency.md](../docs/internals/verification-efficiency.md)
describes what each clause reads.

## Scaling tests

The deterministic multi-size work regressions live in `src/scaling_tests/`,
mirroring `src/`, each included into a `scaling_tests` module of the module it
measures; `cargo nextest run --lib -E 'test(/scaling_tests/)'` runs them all
(`docs/internals/testing.md`, "Scaling tests"). Most measure one kernel
operation beside unrelated state built in advance, and such tests pass while
`heap_objects` grows, because its extra state comes from the proof itself.
End-to-end, `src/scaling_tests/surface/tests/step_shape_scaling_tests.rs`
runs the `scripts/step-scaling-hunt.py` shapes in the gate: a step repeated at
several positions must not drift with the statements before it, and a call
must not grow with unrelated facts, aliases or owned objects; `unfold` and
`fold` tactics are held to the same no-drift rule as steps. Step work does not
capture the uncharged costs of cause 4; the hunt script's mean step time does.
`heap_object_stores_and_releases_cost_the_same_at_every_position` holds
`heap_objects` flat; `sequential_loop_clauses_cost_the_same_at_every_position`
holds the loop bug's clause work flat at five loops.

## Acceptance

- Each remaining cause above is fixed in its representation, with a
  deterministic regression at four or more sizes: the composition scans
  outside stores and separation (cause 2), calls beside held instances or
  composites whose bodies read memory, a condition or a witness (cause 3),
  and evidence checking's premise walk and memory comparisons (cause 4),
  charged once linear work is gone.
- `step-scaling-hunt.py` shows every simple step of every shape constant in
  N, up to logarithmic factors and work proportional to the step's own
  effect (as the final `return` ending N locals in `heap_objects` is).
- No budget or threshold is raised to get there.
