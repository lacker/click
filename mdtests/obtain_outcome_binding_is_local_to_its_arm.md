# Reusing an obtain name after an outcome proof arm

```c filename=obtain_scope.c
int reuse_name(int n) { return n; }
```

```click
verifying "obtain_scope.c";

int32 reuse_name(int32 n) {
    requires exists (k: int32) { k < n };
    ensures exists (k: int32) { k < result };
} by {
    step_until(function.exit);
    if result == n {
        let k = obtain(exists (k: int32) { k < n });
        have k < n by close();
    } else {
    }
    let k = obtain(exists (k: int32) { k < n });
    witness(k);
    close();
}
```

```expect
pass
```
