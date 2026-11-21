# A witness cannot skip a focused resource claim

```c filename=witness_claim.c
int f(int *p, int n) { return n; }
```

```click
verifying "witness_claim.c";

int32 f(int32* p, int32 n) {
    owns *p;
    ensures exists (k: int32) { k == result };
} by {
    step_until(function.exit);
    witness(n);
    known();
}
```

```expect
fail: requires the focused claim to be a proposition
```
