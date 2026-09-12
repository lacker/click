# A loop body that `continue`s cannot close its invariants

A `continue` does reach the loop's back edge, so unlike the `break` of
[`loop_body_break_rejected.md`](loop_body_break_rejected.md) it is the back
edge the invariants should close at. The loop tactic does not see it that way:
the statement stays ahead of the frontier, and `close_invariants()` is refused
whether it is placed before the `continue` or after stepping it.

Linux's `__rb_insert` uses `continue` for both uncle-red cases, the ones that
recolor and climb two frames, so this refusal is the second half of what stops
[`rb_insert_color.md`](rb_insert_color.md).

```c filename=count_down.c
int32 count_down(int32 n) {
    int32 i = n;

    while (i > 0) {
        i = i - 1;
        continue;
    }
    return i;
}
```

```click
verifying "count_down.c";

int32 count_down(int32 n) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        invariant i >= 0;

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: `close_invariants by` requires the loop back edge
```
