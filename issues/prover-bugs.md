# Repair the prover boundaries blocking symbolic arena allocation

## Status, scope, and dependency

P1 tooling blocker for [arena ownership](arena-resource-ownership.md). This
issue owns the concrete resource-lowering, fact-presentation, atomic-search,
and mid-execution `have` defects below. It does not require completing
[legacy cleanup](legacy-cleanup.md). Complete the numbered work packages in
this issue as separate green commits, then resume the broader arena issue.
Do not merge the old investigative patch wholesale.

The C in `examples/arena/arena_alloc.c` is fixed. Do not change it, weaken its
claimed ownership, specialize symbolic endpoints back to constants, add
proof-only C, or increase stack sizes or verification budgets.

The earlier narrative is available at
`ad691bd9:issues/prover-bugs.md`. It is historical evidence, not an authoritative
root-cause analysis. Review inspected `9617be1f` and `092c8599`. Symbol names
below are navigation anchors; line numbers are deliberately omitted.

## Violated invariants

1. A consumer that already has a checked proposition must use that exact
   proposition, with its binder, scope, and memory interpretation. Resolving
   its source spelling again must not silently substitute another fact.
2. An operation introducing facts must return their declaration correspondence
   even when a proposition was already present. Semantic additions and
   presentation/export records are different things.
3. Search must make measurable progress and honor its budgets. Successful
   `extract` is not evidence that the particular premise search wanted was
   extracted. Ordinary inputs must not abort profiling with stack overflow.
4. A simple `have` must share the persistent fact store. Its cost must not
   grow with unrelated accumulated facts or repeatedly rebuild their indexes.
5. Instantiation substitutes into the selected universal. Moving its result
   to another memory snapshot requires checked preservation/equality evidence;
   a matching source spelling is insufficient.

These are separate contracts. No repository-wide `FactId` migration, public
proof syntax change, or blanket prohibition on lowering is required.

## Evidence established during review

- A fresh build of `9617be1f` verifies the committed fixed-size second-allocation
  proof. The stashed symbolic sidecar fails in about one second at unfold with
  `instance body fact needs an unsupported conditional proof`.
- The small resource reproduction below fails at its first `unfold` on that
  build. It does not need an allocator, loop, arithmetic search, or C store.
- Applying the historical investigative source patch and symbolic sidecar to
  `092c8599` makes that small reproduction verify, but the arena proof still
  exhausts the ordinary 2-second smart-tactic limit. Observed goals included
  `prefix != capacity` and `i + 1 <= prefix`. This run did enforce its limit;
  do not cite it as evidence that the ordinary verifier ignores deadlines.
- Profiling that investigative tree aborts with stack overflow. The crash
  trace contains 330 consecutive `try_typed_atomic_simp_closure` frames, above
  `checked_have_with_proof -> check_mid_execution_have`. The recursive edge is
  the retry after `extract_special_conjunct_premises`.
- A temporary diagnostic checking exact membership immediately after that
  extraction reports that `extract(0 <= i)` succeeded without installing the
  selected exact kernel premise. This confirms a no-progress retry, rather
  than merely a large but finite certificate traversal. The diagnostic is
  investigative evidence, not a proposed production implementation. With the
  check, profiling returns a bounded 30-second incomplete run instead of
  aborting; this does not establish that the remaining proof is correct or
  fast. No verifier/profile workers remained after these bounded runs.
- The arithmetic rule and fact-store rebuilding defects described below are
  directly visible in production code, independent of the historical patch.

The local forensic stash object is
`16be558e903b963a3e8ca053cef0dc9823028cc4`; its first parent is the experiment's
base. It includes both the sidecar and speculative verifier changes. Use
`git show OBJECT:PATH` or inspect its diff in a disposable worktree if the
object is available. Never depend on a moving `stash@{0}`, pop the stash, or
make this object the only regression. The small source example and test
recipes here are sufficient to start without it. Do not treat the patched
arena proof as a known-correct completed proof.

## Small reproduction to turn into an mdtest

Use the following unchanged C as `resource.c`:

```c
int32 unchanged(int32* occupied, int32 capacity) { return 0; }
```

Use this sidecar. It describes a resource representation change, not evidence
that a synthetic C function verifies the complete arena allocator.

```click
spec enum PrefixTag { End(int32) }
resource partition(occupied: int32*, capacity: int32) {
    field tag: PrefixTag;
    match tag {
        PrefixTag::End(prefix) => {
            owns occupied[0..capacity];
            fact 0 <= prefix;
            fact prefix <= capacity;
            fact forall (k: int32) {
                0 <= k and k < prefix implies occupied[k] == 1
            };
            fact forall (k: int32) {
                prefix <= k and k < capacity implies occupied[k] == 0
            };
        },
    }
}
verifying "resource.c";
int32 unchanged(int32* occupied, int32 capacity) {
    owns part: partition(occupied, capacity);
    requires 0 <= capacity;
    ensures result == 0;
} by {
    match part.tag {
        PrefixTag::End(prefix) => {
            unfold(part);
            let part = fold(partition(occupied, capacity), {
                tag: PrefixTag::End(prefix)
            });
            step();
            simp();
        },
    }
}
```

Intended result: pass, including independent verification of expansion. At
review baseline the result is a prompt conditional-body-fact refusal. Add the
regression with its fix; do not check in a failing ordinary fixture. If an
intermediate quarantine is unavoidable, follow the existing issue-linked
quarantine mechanism and remove it before this issue closes.

## Work package 1: stop atomic extraction from retrying without progress

Files: `src/surface/proof/smart_closures.rs`, especially
`try_typed_atomic_simp_closure`, `extract_special_conjunct_premises`,
`selected_simp_derivation_with_surfaces`, and `available_surface_fact`.

The current helper decides that extraction happened from the success of
`apply_step(Extract(surface))`. The recursive caller then selects a new
atomic derivation. A current-state spelling can extract a different
snapshot-relative premise; the original wanted premise remains a proper
conjunct and is selected again indefinitely.

Implement the following algorithm:

1. Select one atomic derivation and retain its exact premise list.
2. For each selected premise that needs extraction, resolve a scoped spelling
   for that premise, apply the ordinary checked extraction, and require that
   the successor actually makes that selected premise available at top level.
   A polarity normalization must be an explicitly checked conversion if the
   extraction publishes a different proposition; do not pretend it is the
   same fact.
3. If the required premise was not produced, abandon this candidate promptly
   with bounded diagnostic context. Do not recurse, append another identical
   extraction, or count provenance depth as semantic progress.
4. Check the originally selected derivation against the resulting descendant.
   Do not rerun atomic selection recursively just to discover the extracted
   premises. The loop visits only the finite selected premise list and charges
   its work to the existing tactic budget.

Retain the actual checked steps for expansion. A planner miss must not publish
its partially modified descendant to another candidate.

Tests in `proof_object/tests.rs`: construct a resource conjunction containing
an old-snapshot leaf and a source map whose unqualified spelling denotes a
different current-snapshot leaf. Exercise selection/extraction and assert a
prompt miss or an exact justified conversion, no repeated extraction, and no
change to a sibling proof. Also cover the successful exact-leaf case. Run the
helper and its proof/certificate destruction on the existing 1.75 MiB
small-stack test convention. This is a targeted progress test, not a project
to rewrite every recursive AST visitor; broader source-depth hardening remains
in `surface-unbounded-recursive-depth.md`.

## Work package 2: repair resource lowering and return clause-owned results

Files: `src/kernel/functions.rs` functions
`rewrite_resource_instance_selecting_children` and
`matched_resource_instance_case_facts`; the checked path selector is
`exactly_selected_spec_proposition_path` in `src/kernel/api.rs`.
Consumers include `src/surface/proof/proof_object/resource_steps.rs` and
`src/surface/proof/resources.rs`.

Both resource paths currently require a raw singleton lowering and fail to
extend `body_assumptions` with each preceding established body proposition.
Share a narrow body-clause lowering helper between match publication and
unfold/fold so the two paths cannot diverge again:

- Select a candidate only when its routing facts are checked and selection is
  unique, using the existing exact selector. Continue to discharge every
  lowering/loadability obligation. Never choose the first candidate or a
  survivor merely because other candidates look inconsistent.
- Process clauses in declaration order. On unfold/match, preceding clauses
  are justified by the checked selected resource body. On fold, establish
  each clause before adding it to the context for subsequent clauses. Never
  let an unproved clause justify itself or a later clause justify an earlier
  one. Definition validation remains responsible for legal contained reads.
- Return a named result rather than another positional triple. It should carry
  the successor state, the semantic fact delta, and ordered body-clause
  records. Each record identifies the selected arm and clause ordinal, exact
  lowered proposition, and the binder/lowering introduction information
  needed to present it. The kernel record must not contain Surface syntax.
- Keep a clause record even when inserting its proposition adds no new fact.
  Pair source declarations with these records at the language boundary. Do
  not recover the correspondence from the final fact vector, set membership,
  source-text search, or a second lowering after cell materialization.

Keep the existing ownership boundary for matched arms with child instances:
matching a model must not implicitly unfold child ownership. Only publish
what the selected checked operation authorizes.

Tests: the reproduction above; match-only exposure before unfold; explicit
symbolic-index instantiation using an exposed fact; unfold/refold; a selected
non-first conditional path; ambiguous and unrouted alternatives; a dependent
loadability clause lacking its required scalar bound; and a false fold body
fact. Use kernel unit tests for path selection/obligation details that would
otherwise need contrived source. Existing anchors are
`resource_match_quantified_fact_round_trip.md`,
`resource_match_quantified_fact_rejects_changed_load.md`, and
`resource_match_payload_memory_endpoint.md`.

## Work package 3: preserve selected premises through loops and certificates

Files: `src/kernel/loops.rs::assume_invariant_checks`,
`src/kernel/api.rs::CLoopPreservationContext`,
`src/surface/proof/execution_planning/loop_planning.rs`,
`src/surface/proof/language_context.rs`,
`src/surface/proof/surface_lowering.rs`,
`src/surface/proof/surface_certificates.rs::lower_surface_atomic_derivation`,
and `src/surface.rs::SurfacePropositionMap`.

The loop preservation planner re-lowers invariant declarations to recover
loop-head facts. Return ordered invariant results from the kernel producer
and carry them through `CLoopPreservationContext`, using the same distinction
between clause records and new-fact deltas as resource lowering. Do not use a
suffix of ambient facts or filter out already-known invariants.

Certificate lowering already receives `(kernel, surface)` premise pairs, but
its `availability_kind` discards `kernel` and calls `available_kernel(surface,
available)`. Make the selected kernel proposition the input to validation.
Check that the spelling denotes that input at the output location; if it does
not, use a justified anchored spelling or reject that candidate. Do not just
reverse the lookup order or prefer the newest/oldest match.

Use scoped presentation records keyed by the selected semantic proposition
and its lowering scope. The implementation may reuse persistent maps and
opaque scope tokens already present. Equal exact propositions may share a
semantic key even if proved twice; a proof-event ID is not required. Do not add
deep `CState` equality checks
per citation. Lexical loop-entry records are valid in that entry scope; they
must not silently change what unqualified `a[i]` means after a C store.
Unqualified source citations still mean what the source environment says.
Generated historical citations may use ordinary `old(...)`/`at(...)` syntax;
the user should not have to write arbitrary marks to compensate for a bug.

`available_kernel_matching` already rejects two available matches. Preserve
that ambiguity check. Also distinguish a presentation hint from evidence that
a proposition is available: the map can contain lowerings of unproved goals.

Instantiation stays a substitution operation. Do not adopt the stashed
`with_checked_instantiation_load_presentation` approach that opportunistically
adds the current goal inside `apply_instantiate`. Reuse existing checked
`transport`/equality operations for genuinely different memory snapshots and
retain those operations in the certificate. If no memory change occurred,
retain the original load/binder correspondence rather than reminting it.

Tests: identical spellings with different snapshots and binders; duplicate
loop invariant clauses; one fact with two valid spellings; an unavailable
selected fact with an available equal-looking historical fact; and a
serialized premise with changed snapshot, binder, or polarity. Wrong-state
loads after a write must be rejected. Extend `loop_stable_invariant_export.md`
and the existing changed-load negative rather than replacing their coverage.

## Work package 4: remove ambient rebuilding from mid-execution have

Files: `proof_object/execution_statements.rs::apply_mid_execution_have`,
`checked_drivers/tactic_laws.rs::{check_mid_execution_have,checked_have_with_proof}`,
`proof_object/construction.rs::for_fixed_state`,
`proof_object/splits_and_scopes.rs::begin_have`,
`proof_object/scope.rs::join`, and the callers in
`checked_drivers/proof_execution.rs` (all under `src/surface/proof/`).

The fallback currently materializes `self.facts().to_vec()`, clones that
vector, rebuilds `ProofFacts::from_ordered`, and constructs another lowering
context. A smart miss can then construct a Surface plan and check it again.

Route explicit and smart frontier `have` through a nested scope of the same
persistent `Proof`. Lower the written goal once in the proper lexical scope;
share the facts, effects, requirement index, and snapshot maps. Explicit bodies
run the authoritative checked driver. Smart bodies search checked descendants
under the existing budget. Join retains the exact completion and provenance.
Carry only the produced fact delta into execution evidence and expansion.

Port any missing capability of the old mid-execution route into these checked
operations, not into a second adapter or another fixed-state root. Preserve
match payload bindings, function-entry requirements, predicate unfolding,
selected separation facts, effect-based availability, and source-site
attribution. Use existing indexed effect/requirement queries; moving an
ambient scan into `begin_have` is not a fix. Delete the superseded
mid-execution fallback and its sole-purpose planner/certificate helpers once
the last relevant caller is migrated. General pure-theorem and outcome-drain
migration belongs to `legacy-cleanup.md`.

Deterministic regressions must isolate the operation being measured: construct
prefix contexts with 8, 16, 32, and 64 unrelated facts outside the measured
region, then perform the same explicit `have`. Also measure a sequence of N
simple haves over growing history. Count materialized/indexed fact entries and
checked operations, not only wall time or persistent allocations. The first
curve must be independent of ambient size up to indexed lookup factors; the
whole sequence must be near linear, not quadratic. Include nested have,
matched bindings, sibling isolation, and expansion attribution tests.

## Work package 5: direct arithmetic lookup and integration

In `src/kernel/assumptions/proposition_reasoning.rs`, the
`Int32IncrementUpperBound` evidence arm calls
`exact_signed_order_path_evidence` then accepts only a singleton path. Replace
that selection with the existing `exact_direct_order_step(base, upper, true)`.
Preserve its original premise/polarity evidence and the ordinary checker. Do
not modify the transitive-order search algorithm or expand arithmetic rules.
Test direct and normalized-polarity edges, absence of the required edge, and
8/16/32/64 irrelevant order facts; only the direct rule's work is measured.
This small independent commit may land before the other packages.

For final integration, use the existing arena C and parameterize the occupied
prefix and allocation count. The bounded proof may assume a retained prefix
`p`, `0 <= p <= capacity`, occupied `[0,p)`, zero `[p,capacity)`, a positive
`count`, defined `p + count`, and `p + count <= capacity`. Keep the old live
data prefix owned by the caller; transfer exactly `[p,p+count)` to the new
region and retain the suffix. Start with `live_regions == 1` and prove its
increment to two. This is an explicitly restricted successful-allocation
regression, not completion of invalid-count, exhaustion, arbitrary-hole,
free/recombine, or full arena lifecycle support. Those remain in the arena
issue. Keep the existing fixed-size failure coverage.

Use natural explicit operations and small, relevant smart steps. A remaining
prompt smart miss may be replaced with an explicit valid proof; do not require
an arbitrary historical `simp()` strategy to become complete. Conversely,
never route around an explicit operation losing evidence or a failing
expansion by changing the C or adding irrelevant proof bookkeeping.

## Gates and completion

For each package, add its focused tests and run `scripts/check.sh` in the task
worktree before integration. Use the script's exit status. Once the source
regressions verify normally, run `click profile`, `click expand`, ordinary
verification of the expanded source, and `click audit` on the selected
regressions/claims. Use the CLI's checked `--output`/`--in-place` facilities.
Do not expand an incomplete proof. After a timeout/abort, verify that its
process tree has exited before trusting another measurement.

This issue is complete when:

- The small resource, fact-selection, extraction-progress, and symbolic arena
  regressions pass, with negative/tampering companions rejecting bad evidence.
- The extraction retry cannot recur without establishing its selected premise;
  verify/profile agree and the small-stack regression does not abort.
- Resource and invariant records preserve declaration correspondence without
  re-lowering to recover authority; instantiation does not guess a goal.
- Mid-execution have and the direct arithmetic rule meet the deterministic
  scaling requirements, and their replaced compatibility code is deleted.
- Expansion independently verifies and audit passes for the added positive
  proof sites; relevant architecture documentation matches the implementation.
- `scripts/check.sh` passes. Remove this issue and its index entry, leave
  `legacy-cleanup.md` open, and resume `arena-resource-ownership.md`.
