# An unavailable subtraction equality cannot rewrite a machine index

```c filename=rw.c
unsigned int pick(unsigned int *xs, unsigned long n, unsigned long r) {
    return xs[n - 1];
}
```

```click
verifying "rw.c";

uint32 pick(uint32* xs, uint64 n, uint64 r) {
    requires r == 0u64 and n != 0u64;
    requires n - 1u64 == (n - r) - 1u64;
    views xs[0..n];
    ensures result == xs[(n - r) - 1u64];
} by {
    have xs[n - 1u64] == xs[(n - r) - 1u64] by {
        rewrite(n - 2u64, (n - r) - 1u64);
        close();
    }
}
```

```expect
fail: `rewrite` requires its equality to be an exact available fact
```
