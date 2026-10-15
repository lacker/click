# Split descriptor fold exhausts the simple-checking budget

Priority: P1.

Soundness: incomplete. A supported resource fold cannot finish within its
unchanged deterministic simple-checking budget. This reproduces rejection,
not acceptance of a false postcondition.

## Reproduction and boundary

This blocks activation of the bounded-object-model recovery archive at
`87ad14e1b`. The unchanged original `owned_string_push.c` appends through a
backing pointer, increments the descriptor length, and stores the new zero
terminator through a reloaded pointer. Its resource owns `len`, `cap`, and
`data` separately, owns the backing range, and states descriptor/backing
separation. Whole-struct ownership is a passing control, not the fix.

The focused positive is
[`pointer_field_frame_after_descriptor_and_backing_writes.md`](split-descriptor-fold-exhausts-simple-budget/repro.md).
On the recovery archive, use the identical fixture saved as
[`repro.md`](https://github.com/lacker/click/tree/codex/object-model-failure-reduction/bugs/split-descriptor-fold-exhausts-simple-budget/repro.md):

```sh
click verify bugs/split-descriptor-fold-exhausts-simple-budget/repro.md
click profile --top 12 bugs/split-descriptor-fold-exhausts-simple-budget/repro.md
```

The proof explicitly establishes `0 <= old(owner->len) + 1`, the unchanged
backing pointer, the stored value, and the zero terminator. These all check.
The subsequent `fold(owned_string(owner))` exhausts 750,001 work units against
its 750,000 simple limit. The reduced sidecar reproduces without any other C
function or proof. Moving facts out of the fold's context, increasing limits,
or changing the resource to whole-struct ownership would hide the defect.

The completed profile is an **incomplete diagnostic run**, not a positive
verification or expansion result. Its fold consumed 5.67 seconds before the
budget stopped it. Overlapping completed operation totals within the failed
fold include 721,865 units in offset cancellation, 281,778 in explicit-range
distinctness, 166,175 in recursive range candidates, and 164,103 in membership
offset equality. These totals overlap; they must not be added. This identifies
repeated range/address reasoning, not yet the exact missing cache or index.

The initial missing pointer comparison is narrower than a new object rule:
explicitly proving the nonnegative append index supplies the complete-range
frame check. A hypothesis that retained bindings were necessarily missing was
not established. Preserve original split-field ownership when investigating.

## Acceptance criteria

- The archive verifies the focused fixture and the original string push with
  unchanged C, contracts, and split-field resource definitions.
- Fresh, expanded, rewritten and retained checking all pass at existing limits.
- Wrong stored-value and wrong-terminator claims still reject; missing backing
  ownership must not authorize a write.
- The simple fold performs selected indexed work rather than recursive ambient
  address search; protect a performance repair with deterministic checks at
  multiple unrelated-context sizes.
- Remove temporary probes. Keep the separate vector allocation-fold failure
  open until its own original case verifies.

## Checked repair candidate

Restricting the preliminary directional byte-gap check to exact recorded order
avoids general arithmetic reasoning recursively resolving the same memory
histories. The original focused split-field proof passes fresh, expanded,
rewritten and retained checks with a rebuilt probe-free CLI/library. All 227
selected archive controls pass, including a multi-size gap-query regression.
Wrong-value, wrong-terminator and missing-backing-ownership controls reject.
The completed profile measures the fold at 0.40s; other simple steps remain
expensive. Current-upstream extraction and validation are in progress. The
separate vector allocation fold and later string-clear proof remain open.
