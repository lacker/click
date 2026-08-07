# Merge deferred tactic expansion across preserved branch contexts

## Problem

A frontier-local `branch` preserves one replay context for each feasible C
arm. A smart tactic in the common continuation can therefore need a different
simple certificate in each context. Expansion now collects and emits a logical
case split for ordinary continuation tactics, but post-execution tactics such
as `simp` are lowered later, during final outcome certification.

The deferred expansion probe currently completes on the first finalized
context. Its certificate can mention that arm's condition, and replay of the
rewrite then fails in the sibling arm. This is an expansion/replay disagreement,
not smart-search incompleteness and not a reason to retain `reach` merely to
erase the path distinction.

## Minimal regression

Use unchanged C with an `if`, a shared arithmetic statement, and a return:

```c
int32 positive_after_branch(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
```

The Click proof should execute the `if` with `branch`, execute the common
suffix, and finish `ensures result > 0` with one source `simp`. Expanding that
`simp` must produce a rewrite which verifies from function entry. Today it can
emit a derivation requiring `x >= 0`, which fails in the C `else` context.

Keep this regression separate from the ordinary common-step regression in
`src/lang/click/expansion.rs`: that case captures while the branch continuation
is replaying and is already supported.

## Design direction

Deferred capture must be an aggregation, not an early-return sentinel owned by
the first finalized replay context:

1. Retain the source branch choice and stable source-site condition for every
   context reaching the selected deferred tactic.
2. Finalize the selected tactic independently in every feasible context.
3. Merge equal certificates. When they differ, emit one logical `if` tree whose
   leaves contain the corresponding simple certificates.
4. Only report capture completion after all sibling contexts belonging to the
   selected proof occurrence have contributed.
5. Reverify the merged rewrite from the original proof boundary.

Do not solve this by omitting exact premises, changing the C, inserting a
source-level case split solely for expansion, keeping a `reach` abstraction,
or accepting a rewrite that only verifies when started inside one arm.

The aggregation should eventually support nested `branch` contexts. A focused
first implementation may handle one enclosing branch, but it must represent
that limitation explicitly and must not silently choose one path.

## Acceptance criteria

- The minimal `branch`/common-`simp` regression expands and reverifies.
- Different arm-local certificates become a replayable logical case split.
- Equal arm-local certificates remain a single certificate.
- An unreachable or returning arm does not invent a missing obligation.
- Nested branches either aggregate correctly or fail with a focused bounded
  diagnostic before returning an expansion.
- Existing proof-level `if`, grouped-contract, deferred closer, expansion, and
  audit tests remain green.

## Blocks

This blocks removing `reach` from examples whose common suffix ends in a
path-dependent deferred tactic. Those migrations should remain unchanged until
this issue is fixed; straightforward non-deferred migrations may proceed.
