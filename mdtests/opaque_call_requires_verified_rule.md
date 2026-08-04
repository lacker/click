# opaque calls may use a later contract in the same verification transaction

The caller is deliberately listed before its callee. Click verifies the closed
call-graph transaction atomically, so source order does not determine whether
the callee contract is available.

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
        step();
        step();
        step();
        simp();
    }
}

int32 helper(int32 x) {
    ensures result == x by auto;
}
```

```expect
pass
```
