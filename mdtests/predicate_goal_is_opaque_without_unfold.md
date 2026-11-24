# a predicate goal is opaque without unfold

The negative of `mdtests/unfold_predicate_selects_one_application.md`.
Without `unfold(small(c))`, the goal `small(c)` is not read through its body,
so the two bounds in the context do not close it.

```click checked-only
predicate small(x: int32) { 0 <= x and x <= 5 }

theorem predicate_goal_is_opaque(c: int32) {
    requires 0 <= c;
    requires c <= 5;
    ensures 0 <= c by {
        have small(c) by close();
        close();
    }
}
```

```expect
fail: `known` requires the current goal as an available semantic fact
```
