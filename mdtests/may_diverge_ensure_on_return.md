# A possibly divergent call promises only its return case

When `flag[0]` is nonzero this C0 function loops forever because nothing can
change the viewed cell. When it is zero, the function and its caller return
zero. The callee contract remains useful on that hypothetical return branch.

```c filename=may_diverge_ensure_on_return.c
int32 wait_while_nonzero(int32 flag[]) {
    while (flag[0] != 0) {
    }
    return flag[0];
}
```

```c filename=call_may_diverge.c
int32 call_wait(int32 flag[]) {
    int32 result;
    result = wait_while_nonzero(flag);
    return result;
}
```

```click
verifying "may_diverge_ensure_on_return.c";
verifying "call_may_diverge.c";

int32 wait_while_nonzero(int32 flag[]) {
    views flag[0..1];

    for loop(0) {
        invariant flag[0] == old(flag[0]);
    }

    ensures result == 0 by auto;
}

int32 call_wait(int32 flag[]) {
    views flag[0..1];
    ensures result == 0 by auto;
}
```

```expect
pass
```
