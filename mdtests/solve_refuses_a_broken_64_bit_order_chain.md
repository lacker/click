# `solve` refuses a broken 64-bit order chain

As `solve_closes_a_64_bit_order_chain.md`, but nothing orders `b` below `c`:
the second fact runs the wrong way, so no chain reaches the goal.

```click quick-solve
theorem broken(a: uint64, b: uint64, c: uint64) {
    requires a < b;
    requires c <= b;
    ensures a < c by { close(); }
}
```

```expect
fail: could not establish `a < c`
```
