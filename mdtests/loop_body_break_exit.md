# A `break` in a loop body is one of the loop's exits

The `loop` tactic certifies one body iteration. A path that ends in `break`
does not reach the back edge and is not asked to: it is an *exit*. The
invariants are not closed on it, no measure is required to decrease on it, and
the facts it established are exported as one disjunct of the loop's single
successor, beside the guard-false exit and beside every other `break`. This is
the join package A17 built for the exits of a short-circuit guard, now fed by
the body as well as by the guard.

`break_once` is the smallest case: the loop leaves either because `i > 0`
failed or because the body broke while `i > 0` held. Both exits stand at the
loop's own exit state, so the rule exports one successor whose facts are the
invariants plus `i <= 0 or i > 0` — and nothing stronger, which is what keeps
a claim such as `result == 0` from being provable here
([`loop_body_break_exit_claim_rejected.md`](loop_body_break_exit_claim_rejected.md)).

`stop_at` is the shape of Linux's `__rb_insert`: `while (true)`, which has no
guard-false exit at all, with every way out a `break` inside an `if`. The
successor is the join of the two `break` exits alone, and the post-loop claim
reads their disjunction.

A `break` path whose state differs from the loop's other exits — one that
assigns or stores before leaving — has no common successor with them and is
refused by name; see
[`loop_body_break_exit_state_rejected.md`](loop_body_break_exit_state_rejected.md).

```c filename=break_once.c
int32 break_once(int32 n) {
    int32 i = n;

    while (i > 0) {
        break;
    }
    return i;
}
```

```c filename=stop_at.c
int32 stop_at(int32 n) {
    int32 i = n;

    while (true) {
        if (i == 3) {
            break;
        }
        if (i == 0) {
            break;
        }
        i = 0;
    }
    return i;
}
```

`break_once_automatically` is `break_once` with both phases omitted: the
automation the `loop` keyword owns walks the body's `break` path itself, so an
exit needs no written proof.

```c filename=break_once_automatically.c
int32 break_once_automatically(int32 n) {
    int32 i = n;

    while (i > 0) {
        break;
    }
    return i;
}
```

```click
verifying "break_once.c";
verifying "stop_at.c";
verifying "break_once_automatically.c";

int32 break_once(int32 n) {
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
        }
    }
    step();
    simp();
}

int32 stop_at(int32 n) {
    requires n >= 0;
    ensures result == 3 or result == 0;
} by {
    step();
    step();
    loop {
        invariant i >= 0;

        initialize by simp;
        preserve by {
            if i == 3 {
                step();
                step();
            } else {
                step();
                step();
                if i == 0 {
                    step();
                    step();
                } else {
                    step();
                    step();
                    step();
                    close_invariants();
                }
            }
        }
    }
    step();
    simp();
}

int32 break_once_automatically(int32 n) {
    requires n >= 0;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
    }
    step();
    simp();
}
```

```expect
pass
```
