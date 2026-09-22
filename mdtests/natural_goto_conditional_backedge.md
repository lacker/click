# `loop` proves a conditional natural `goto` cycle

The back edge may be nested in the entry label's `if` arm. The existing
`loop` tactic still supplies the invariant and termination proof.

```c filename=natural_goto_conditional_backedge.c
int32 maybe_stop_conditional(int32 flag) {
again:
    if (flag > 0) {
        flag--;
        goto again;
    }
    return 0;
}
```

```click
verifying "natural_goto_conditional_backedge.c";

int32 maybe_stop_conditional(int32 flag) {
    requires flag >= 0;
    ensures result == 0;
} by {
    loop {
        invariant flag >= 0;
        decreases flag;
    }
    simp();
}
```

```expect
pass
```
