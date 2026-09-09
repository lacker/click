# Preserve initialization requirements across resource transfers

P1 soundness bug, split from bug bash #8. Confirmed at `7bdfaaa5` on 2026-09-08: the following expected rejection instead verifies.

Invariant: permission to read or own storage does not establish that its contents have been initialized. Passing a never-written local through a verified contract must not manufacture initialized values.

# Reject passing uninitialized storage to a reading callee

```c filename=t.c
int32 same_twice(int32* p) {
    return p[0] == p[0];
}
int32 uninit_eq_callee() {
    int32 x;
    return same_twice(&x);
}
```

```click
verifying "t.c";
int32 same_twice(int32* p) {
    views p[0..1];
    immutable;
    ensures result == 1 by auto;
}
int32 uninit_eq_callee() {
    ensures result == 1 by auto;
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```

Acceptance: reject this unchanged C with an uninitialized-storage diagnostic; retain positive initialized-call cases and write-only callees that initialize an output. Check both views and owns transfers. Carry/check initialization evidence at the call boundary without confusing allocation bounds with initialized contents. Full scripts/check.sh must pass. Delete this issue and its index entry when fixed.
