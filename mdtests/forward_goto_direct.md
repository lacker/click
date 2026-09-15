# direct forward goto

A direct function-body `goto` may skip ordinary statements and resume at a
later direct function-body label. It preserves the current C state.

```c filename=forward_goto_direct.c
int32 forward_skip(void) {
    int32 value;
    value = 1;
    goto done;
    value = 99;
done:
    return value;
}

int32 forward_skip_execute(void) {
    int32 value;
    value = 1;
    goto done;
    value = 99;
done:
    return value;
}

int32 forward_goto_chain(void) {
    int32 value;
    value = 0;
    goto first;
    value = 90;
first:
    value += 1;
    goto second;
    value = 99;
second:
    return value + 1;
}
```

```click
verifying "forward_goto_direct.c";

int32 forward_skip() {
    ensures result == 1;
} by {
    step();
    step();
    step();
    step();
    normalize();
}

int32 forward_skip_execute() {
    ensures result == 1;
} by {
    execute();
    normalize();
}

int32 forward_goto_chain() {
    ensures result == 2;
} by {
    execute();
    normalize();
}
```

```expect
pass
```
