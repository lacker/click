# `solve` proves a byte defined in a symbolic produced range

The call returns an initialized byte range whose length is symbolic.
The caller uses its index bound to prove that the selected byte is defined
after the call.

```c filename=solve_proves_a_byte_defined_in_a_symbolic_produced_range.c
void fill(unsigned char *dst, unsigned long n);

void caller(unsigned char *dst, unsigned long n, unsigned long i) {
    fill(dst, n);
}
```

```click quick-solve
verifying "solve_proves_a_byte_defined_in_a_symbolic_produced_range.c";

extern void fill(uint8* dst, uint64 n) {
    consumes uninitialized(dst[0u64..n]);
    produces dst[0u64..n];
}

void caller(uint8* dst, uint64 n, uint64 i) {
    requires i < n;
    consumes uninitialized(dst[0u64..n]);
    ensures defined(dst[i]);
} by {
    step();
    step();
    close();
}
```

```expect
pass
```
