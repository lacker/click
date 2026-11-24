# `enumerate` refuses an instance held in another spelling

The companion of `enumerate_closes_instances_by_evaluation_or_exact_facts.md`.
An instance that does not evaluate to true must be an exact available fact.
`0 == f(0)` states the `k == 0` instance with its sides swapped, which is not
the instance `f(0) == 0`, so `enumerate` refuses rather than searching for an
equivalent fact. Restate it first, for example with `have f(0) == 0 by
close();`, or prove the instance with `have`.

```click
function f(x: int32) -> int32 { x }

theorem mirrored_instance() {
    requires 0 == f(0);
    requires f(1) == 1;
    ensures forall (k: int32) { 0 <= k and k < 2 implies f(k) == k } by {
        enumerate();
    }
}
```

```expect
fail: `enumerate` requires each in-range instance as an exact available fact
```
