# `solve` refuses definedness one past a symbolic produced range

The initialized range ends before `n`. A pointer one past the range is
valid to form, but the call does not make a byte read at that address defined.

```c filename=solve_refuses_definedness_one_past_a_symbolic_produced_range.c
void fill(unsigned char *dst, unsigned long n);

void caller(unsigned char *dst, unsigned long n) {
    fill(dst, n);
}
```

```click quick-solve
verifying "solve_refuses_definedness_one_past_a_symbolic_produced_range.c";

extern void fill(uint8* dst, uint64 n) {
    consumes uninitialized(dst[0u64..n]);
    produces dst[0u64..n];
}

void caller(uint8* dst, uint64 n) {
    consumes uninitialized(dst[0u64..n]);
    ensures defined(dst[n]);
} by {
    step();
    step();
    close();
}
```

```expect
fail: unclosed goal
```
