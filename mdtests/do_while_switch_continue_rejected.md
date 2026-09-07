# `continue` inside a `switch` is rejected in a call-condition `do ... while`

A `do ... while` whose condition contains a call is lowered to an
unconditional shell whose tail evaluates the condition, and a `continue` gets
the same call-and-check sequence before returning to the shell head. That
check ends a failing iteration with `break`, which a `switch` captures as its
own exit: the rest of the body would run and the loop would not end.

C0 has no spelling for "leave the loop" from inside a `switch`, so the shape
is rejected rather than lowered into different control flow. In C this
function returns 0: the `continue` skips `tail++` and reaches the post-test,
which is false.

```c filename=do_while_switch_continue_rejected.c
int32 stop_now() {
    return 0;
}

int32 do_while_switch_continue_rejected() {
    int32 count = 0;
    int32 tail = 0;
    do {
        count++;
        switch (count) {
            case 1:
                continue;
            default:
                break;
        }
        tail++;
    } while (stop_now());
    return tail;
}
```

```click
verifying "do_while_switch_continue_rejected.c";

int32 stop_now() {
    ensures result == 0;
}

int32 do_while_switch_continue_rejected() {
    ensures result == 1;
}
```

```expect
fail: `continue` inside a `switch` is not supported
```
