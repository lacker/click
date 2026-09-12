# A `break` exit is not assumed to satisfy the invariants

The negative companion of
[`loop_body_break_exit.md`](loop_body_break_exit.md). The loop leaves either
because `i > 0` failed or because the body broke while `i > 0` held, so its
successor states `i <= 0 or i > 0` and nothing more. `result == 0` needs the
failed guard alone, which is exactly the exit this `break` skips: dropping the
break path — the hole S1 closed for a short-circuit guard — would prove a
claim that is false whenever `n` is positive.

The refusal is at the claim, not at the loop: the loop rule itself is fine,
and the proof fails where the postcondition asks the exit for more than the
join states.

```c filename=break_once_claim.c
int32 break_once_claim(int32 n) {
    int32 i = n;

    while (i > 0) {
        break;
    }
    return i;
}
```

```click
verifying "break_once_claim.c";

int32 break_once_claim(int32 n) {
    requires n >= 0;
    ensures result == 0;
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
```

```expect
fail: `ensures result == 0` failed
```
