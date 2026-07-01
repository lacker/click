# Contract Let-Where Bindings

```c filename=identity.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "identity.c";

int32 identity(int32 x) {
    let k: int32 where k == x;

    ensures result_matches_witness: result == k by {
        symbolic_execute();
        witness(k = x);
        simp();
    }
}
```

```expect
pass
```
