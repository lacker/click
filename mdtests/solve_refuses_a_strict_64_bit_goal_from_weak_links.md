# `solve` refuses a strict 64-bit goal from weak links

As `solve_closes_a_64_bit_order_chain.md`, but both links are `<=`: the chain
shows `a <= c`, not `a < c`, and `solve` refuses the strict goal.

```click quick-solve
theorem not_strict(a: uint64, b: uint64, c: uint64) {
    requires a <= b;
    requires b <= c;
    ensures a < c by { close(); }
}
```

```expect
fail: could not establish `a < c`
```
