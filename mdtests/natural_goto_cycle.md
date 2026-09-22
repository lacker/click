# `loop` proves a natural `goto` cycle

The source loop is expressed as a function-body label and a backward `goto`.
The ordinary completion of the cycle body is the return path; the `goto`
itself is the back edge closed by the existing `loop` tactic.

```c filename=natural_goto_cycle.c
int32 maybe_stop(int32 flag) {
again:
    if (flag == 0) {
        return 0;
    }
    flag = 0;
    goto again;
}
```

```click
verifying "natural_goto_cycle.c";

int32 maybe_stop(int32 flag) {
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
