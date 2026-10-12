# Checked reachable calls retain their termination dependencies

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

int32 wait_while_nonzero(int32 flag[]) diverges {
    views flag[0..1];
    ensures result == 0;
} by {
    loop diverges {
        invariant flag[0] == old(flag[0]);
    }
    step();
    simp();
}

int32 call_wait(int32 flag[]) {
    views flag[0..1];
    ensures result == 0 by auto;
}
```

```expect
fail: callee `wait_while_nonzero` has no termination evidence
```
