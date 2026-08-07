# Proof mark names are unique

A proof-local mark cannot be silently rebound to a different frontier state.

```c filename=proof_mark_duplicate.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "proof_mark_duplicate.c";

int32 identity(int32 x) {
    ensures result == x by {
        mark start;
        mark start;
        execute();
        simp();
    }
}
```

```expect
fail: duplicate proof mark `start`
```
