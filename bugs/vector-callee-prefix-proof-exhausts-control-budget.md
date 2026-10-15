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
