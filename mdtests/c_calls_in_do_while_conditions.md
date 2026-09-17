# Calls in do-while conditions run after the body

The condition of a `do ... while` executes after the first body pass and after
an iteration reaches `continue`. The lowering uses an unconditional iteration
shell, placing the checked call prefix after normal body completion and before
each `continue` that targets this loop.

```c filename=call_in_do_while_condition.c
int32 call_in_do_while_condition() {
    int32 count = 0;
    do {
        count++;
    } while (stop_now());
    do {
        count++;
        continue;
    } while (stop_now());
    return count;
}
```

```c filename=stop_now.c
int32 stop_now() {
    return 0;
}
```

```click
verifying "call_in_do_while_condition.c";
verifying "stop_now.c";

int32 call_in_do_while_condition() {
    ensures result == 2 by auto;
}

int32 stop_now() {
    ensures result == 0 by auto;
}
```

```expect
pass
```
