# Give automatic objects fresh lifetime on block re-entry

P1 soundness bug, split from the bug bash. Confirmed at `7bdfaaa5` on 2026-09-08: the following expected rejection instead verifies.

Invariant: an automatic object begins a fresh lifetime whenever its declaration is executed; old stored values and aliases cannot initialize a later lifetime. Local blocks are currently named by declaration and reused across loop iterations.

# Reject reading a previous block entry's automatic array value

```c filename=t.c
int32 f() {
    int32 i;
    for (i = 0; i < 2; i++) {
        int32 a[2];
        if (i == 1) {
            return a[0];
        }
        a[0] = 5;
    }
    return 0;
}
```

```click
verifying "t.c";
int32 f() {
    ensures result == 5;
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```

Acceptance: reject this unchanged C with an uninitialized-storage diagnostic; accept the variant that initializes the element during each block entry. Cover escaped pointers to earlier lifetimes and nested scopes, not only clearing cell values. Preserve symbolic loop verification and full scripts/check.sh. Delete this issue and its index entry when fixed.
