# solve refuses a uint32 predecessor without its guard

`x - 1 <u x` is false at `x == 0`, where the predecessor wraps to
`UINT_MAX`. Without the fact `0 <u x` there is no lemma to apply, and `solve`
leaves the goal open.

```click quick-solve
theorem predecessor_without_a_guard(x: uint32) {
    ensures to_integer(x - 1u32) < to_integer(x) by close();
}
```

```expect
fail: could not establish `to_integer((x - 1u32)) < to_integer(x)`
```
