# Vector callee-prefix proof exhausts the control budget

Soundness: incomplete. A valid prefix-preservation goal exhausts the existing
smart-proof control budget. No false claim is accepted. The corresponding
single-call control verifies with `simp`; the grow-then-push context does not.

Reproduced on recovery checkpoint `1a74b09c5`, not current upstream. Keep the
original C, resources, contracts and work limits. In
[the original vector proof](../examples/owned-vector/vector.click), inside the
successful grow branch's final prefix proof, insert this immediately before
its existing `instantiate` at line 517:

```click
have forall (j: int32) {
    0 <= j and j < at(statement(8).entry, owner->len) implies
        owner->data[j] == at(statement(8).entry, owner->data[j])
} by { simp(); }
```

Run `click verify --trace-proof allocated_vector_push examples/owned-vector/vector.click`.
The `have` exhausts 2,500,000 deterministic control units. This is an incomplete
diagnostic run, not a successful verification or performance profile.
The same callee guarantee is recorded in the environment, but the direct
`instantiate` spelling is not exactly available. The trace stops read comparison
at a four-byte descriptor store after the call. Merely transporting the old
prefix across the call's broad writable footprint is insufficient; the callee's
explicit prefix guarantee must be used.

The smaller [passing control](../mdtests/c_pointer_field_prefix_postcondition_across_call.md) copies the unchanged `vector_push.c`, its `vector_storage`
resource and original contract/proof, and adds a caller that returns
`vector_push(owner, value)`. The caller owns `vector_storage`, requires
`owner->len < owner->cap`, and ensures the same old-prefix equality. Its proof
`execute(); assumption(); simp();` verifies; replacing `simp` by `assumption`
rejects exact-fact lookup, which is expected. This control passes fresh, expanded, rewritten and retained checking on the
clean recovery build. It does not reproduce the budget failure. The defect has not yet been reduced to its essential state
delta, and no asymptotic cause has been established.

A diagnostic `CLICK_TIMINGS=1` rerun reproduces the same refusal. Its nested
operation records attribute 1,151,442 deterministic units to `simp selected
premise reduction` (5.89s observed) within the failing claim's 2,749,799 units
of post-execution tactics. Inclusive operation totals overlap and must not be
added. Source inspection finds legacy atomic-evidence premise minimization
trying up to 255 restricted queries for up to 128 selected facts. This is a
candidate cost to isolate, not an established asymptotic defect or justification
to disable certificate checks.

A private isolation run skipped premise shortening but retained proof
validation and the same budgets. It still exhausted 2,500,000 units, then
inside snapshot transport (about 1.13 million units) and quantified framing
(about 422,000 nested units). The completed distinctness/range-membership
operations dominate that refusal. Premise minimization is therefore not a
sufficient fix. The private switch was removed; neither isolation run is a
successful proof or accepted performance result.

Acceptance criteria:

- Reduce the grow-then-push state dependency and identify the checked callee
  guarantee's read carriers; do not increase budgets or infer pointer identity
  from numeric equality.
- Make the original source and claims verify with a bounded explicit proof or
  repair the selected checker/search defect demonstrated by the reduction.
- Retain fresh, expanded, rewritten and retained checks and negative controls
  for wrong prefix values, overlapping writes and missing authority.
- Add deterministic multi-size regressions if a performance-sensitive path
  changes. Distinguish this failure from the separately tracked successful
  string return-resource proof cost; their causes are not established equal.

## Checked call-return frontier prerequisite

Stateful ensures are now also instantiated at the returned memory after
body-certified pointer effects and output checks. The small modular control
passes fresh, expanded, rewritten and retained checks using exact assumptions;
401 selected call-contract, C++ and rewrite controls pass. The original vector
prefix obligation is not closed by this repair. Its post-call descriptor-store
frame checks individually, but reusing checked equalities in the nested proof
still exposes repeated lowering. Keep this report open.

## Nested spelling repair and precise budget stack

The shared proof object now retains checked transport and instantiation
spellings in nested fixed-state/outcome propositions. It validates fact
availability on lookup and freezes evaluated arguments across `old`/`at`.
Two 0/16/64/256 controls reject absent authority, missing guards and rebound
proof names; all 402 selected recovery controls pass. The independent PR #1081
passes its two controls, 107 logical controls and the full normal Markdown
corpus on upstream.

The reduced vector proof explicitly instantiates the push prefix guarantee,
frames the post-call and pre-call reads separately, and rewrites the resulting
equalities. It progresses past the previous rewrite-lowering failures, but
still exhausts the unchanged enclosing control budget. The error points to
the outer `have`; a full debugger stack corrects the apparent localization.
At exhaustion, `apply_fixed_state_transport_using` is inside
`ProofFacts::available_across_effects` / `exact_available_across_effects`, then
`condition_bridged_fact_is_available`, origin-unchanged memory equivalence,
typed store separation, and range membership. The snapshot-blind bucket is
indexed, but trying its historical equality candidates is expensive before
the requested frame is checked. This is not evidence that scope closing or
publication caused the failure. No successful full vector proof is claimed.
