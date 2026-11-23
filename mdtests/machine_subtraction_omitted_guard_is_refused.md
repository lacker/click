# An omitted subtraction bound remains an unproved guard

```c filename=inst.c
unsigned int at(unsigned int *xs, unsigned long n, unsigned long r) {
    return xs[n - r];
}
```

```click
verifying "inst.c";

uint32 at(uint32* xs, uint64 n, uint64 r) {
    requires 0u64 < r and r <= n;
    requires forall (k: uint64) { k < n implies xs[k] <= 100u32 };
    views xs[0..n];
    ensures result <= 100u32;
} by {
    have xs[n - r] <= 100u32 by {
        instantiate(forall (k: uint64) { k < n implies xs[k] <= 100u32 }, n - r);
        known();
    }
}
```

```expect
fail: `known()` could not close the current goal
```
