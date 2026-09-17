# Calls in while and for conditions are reevaluated

Calls in a reevaluated loop condition must remain inside the loop rather than
being hoisted before it. The lowering uses an unconditional iteration shell,
executes the checked call at the top of each iteration, and breaks when the
condition is false.

```c filename=call_in_while_condition.c
int32 call_in_while_condition() {
    while (stop_now()) {
        return 1;
    }
    return 0;
}
```

```c filename=call_in_for_condition.c
int32 call_in_for_condition() {
    for (; stop_now();) {
        return 1;
    }
    return 0;
}
```

```c filename=stop_now.c
int32 stop_now() {
    return 0;
}
```

```click
verifying "call_in_while_condition.c";
verifying "call_in_for_condition.c";
verifying "stop_now.c";

int32 call_in_while_condition() {
    ensures result == 0 by auto;
}

int32 call_in_for_condition() {
    ensures result == 0 by auto;
}

int32 stop_now() {
    ensures result == 0 by auto;
}
```

```expect
pass
```
