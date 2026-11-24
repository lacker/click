# a natural `goto` cycle's `return` exit is a function exit

`maybe_stop(0)` returns `7`. The cycle is lowered to `while (1) { body }`,
and the returning preservation path used to be offered to the kernel as a
state at which the guard is re-read: `1` is never false, so the rule's only
path was `VerificationDiverges` and `ensures result == 0` was discharged
vacuously. The return is now a `Return` outcome of the loop rule and reaches
contract certification with its value.

```c filename=a_natural_goto_cycle_return_exit_is_a_function_exit.c
int32 maybe_stop(int32 flag) {
again:
    if (flag == 0) {
        return 7;
    }
    flag = 0;
    goto again;
}
```

```click
verifying "a_natural_goto_cycle_return_exit_is_a_function_exit.c";

int32 maybe_stop(int32 flag) {
    requires flag >= 0;
    ensures result == 0;
} by {
    loop {
        invariant flag >= 0;
        decreases flag;
    }
    close();
}
```

```expect
fail: result == 0; left side evaluated to 7
```
