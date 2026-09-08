# Plan quantified invariant bodies without stack overflow or legacy discovery

## Violated invariant

Automatic preservation must emit a complete checked proof of the exact
back-edge value and safety obligations. It cannot depend on hidden legacy
invariant discovery after expansion. Its ordinary bounded search must report
a local miss, not overflow the verifier stack.

The context-bound `close_invariants by { ... }` evidence interface is already
implemented. The remaining gap is constructing its proof, not accepting it.
This blocks the automatic-planning part of
[loop closure migration](loop-closure-quantified-evidence.md).

## Reproduction at the green checkpoint

`explicit_invariant_body_copy3_planning_census` verifies the
unchanged `mdtests/copy3_array_demo.md`, expands its grouped claim, and replaces
only `close_invariants();` with `close_invariants by { simp(); }`. The resulting
proof currently overflows the ordinary test stack even with all automatic
planner prototypes reverted. The new regression is explicitly ignored until
the crash is fixed; no existing test or fixture is quarantined. Run it with:

```sh
cargo nextest run --lib --run-ignored only -E 'test(explicit_invariant_body_copy3_planning_census)'
```

The baseline crash includes recursive `derive_proposition_using`, quantified
instantiation, and atomic premise selection under the explicit closure-body
driver. Restore this test to the ordinary gate when verification and expansion
pass. Never edit the fixture's C or increase stack limits to bypass this gap.

## Automatic-planner investigation (2026-09-08)

The attempted replacement in `verify_one_loop_preservation_proof` removed
`legacy_loop_invariant_prefix_holds` and planned a body through the same
kernel-created scope as written bodies. Scalar tests passed. Bubble required
the existing named invariant lemmas to be proved at the execution frontier
before opening that scope. Proving them inside the already-created scope did
not discharge the original quantified goal. With frontier lemmas, the original
and expanded bubble fixture passed with zero legacy discovery calls.

Copy3 still failed. Its collected goals include current and old source-read
safety, destination-read safety, and wrapped quantified copy equalities.
`synthesize_surface_proposition` cannot present the old-state equality goals;
the missing presentation also hides the enclosing conjunction from structural
planning. Using `synthesize_surface_proposition_at_entry_and_post` with
`ExecutionProofContext::old_reference_state` exposes more of the goal, but
ordinary verification then overflowed the default test stack.

The crash stack contained roughly a dozen repeated structural-simp / smart
closure frames, followed by upper-bound splitting, quantified premise
selection, loadability reasoning, and capture-free substitution. The worker
exited after the abort. No stack or tactic limits were raised.

An explicit pending-join traversal for conjunctions avoided that observed
overflow, but skipped intermediate atomic/direct closure opportunities. It
increased search substantially and still failed copy3's quantified proof.
That is not a finished fix or an acceptable performance result. All runtime
prototypes were reverted; no failing planner or traversal is enabled.

## Next implementation

1. Preserve exact entry/current snapshot presentation for each lowered goal.
   Do not equate goals by their printed spelling or a snapshot-blind binder key.
2. Make conjunction planning stack-safe while preserving the cheap closure
   opportunities at intermediate nodes. Add a deterministic four-size
   regression and an ordinary-or-smaller-stack regression, including quantified
   leaf work; a large stack is not a remedy.
3. Construct the missing copy3 value proof with checked operations in the exact
   goal scopes. Named lemmas may be premises only after their proofs complete.
   Separately retained read-safety goals must not become assumptions.
4. Enable automatic bodies only once the unchanged copy3 and bubble fixtures,
   their expansions, and the full gate pass without legacy discovery. Preserve
   do-while paths with no continuing back edge.

## Acceptance criteria

- Original copy3, bubble-pass, and sorting fixtures verify and expand to
  explicit closure bodies; expanded proofs recheck without legacy back-edge
  discovery (`invariant_discovery_calls` supplies a test counter).
- Missing child/value/safety evidence and wrong snapshot/premise roots reject.
- Quantified conjunction planning is bounded, stack-safe, and has deterministic
  scaling coverage without dropping existing useful closure strategies.
- The ignored reproducer is enabled and `scripts/check.sh` passes. Delete this issue and its index line when the
  positive regressions and documentation land.
