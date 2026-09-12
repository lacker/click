# A `continue` in a loop body is the loop's back edge

Unlike the `break` of
[`loop_body_break_exit.md`](loop_body_break_exit.md), a `continue` does reach
the loop's back edge, so it is the back edge the invariants close at. The rule
is the one the body's end already had, applied one statement earlier: the
loop's binders are bound again on the state the `continue` reached, the
invariants are closed there, and a declared measure must have descended there.
`close_invariants()` is written at the `continue`, after stepping it, exactly
as it is written at the body's end.

Linux's `__rb_insert` uses `continue` for both uncle-red cases, the ones that
recolour and climb two frames. `count_down` is that shape reduced to one
statement and a `continue`.

A `continue` under a structural measure is
[`loop_body_continue_structural_measure.md`](loop_body_continue_structural_measure.md);
a `continue` that does not hand its binder back is refused by name in
[`loop_body_continue_drops_binder.md`](loop_body_continue_drops_binder.md).

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
            have 0 <= i - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(i)) using { i > 0; }
            }
            step();
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
