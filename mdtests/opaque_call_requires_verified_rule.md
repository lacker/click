# opaque calls require an already verified rule

The caller is deliberately listed before its callee. Click must report the
missing verified rule instead of silently stepping into the callee body.

```c filename=caller.c
int32 caller(int32 x) {
    int32 y;
    y = helper(x);
    return y;
}
```

```c filename=helper.c
int32 helper(int32 x) {
    return x;
}
```

```click
verifying "caller.c";
verifying "helper.c";

int32 caller(int32 x) {
    ensures result == x by {
        execute_step();
        execute_step();
        execute_step();
        simp();
    }
}

int32 helper(int32 x) {
    ensures result == x by auto;
}
```

```expect
fail: cannot execute call to `helper` opaquely: its contract has not been verified yet
```
