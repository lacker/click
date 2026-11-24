# solve closes single unsigned steps

An unsigned order is a `uint32` order, whose wrapping steps `solve`'s
arithmetic does not relate. A goal that is one step of
`uint32` arithmetic from an exact fact is closed with the lemma that states
that step, so `solve` does not need the lemma named.

```click
theorem predecessor(x: uint32) {
    requires x > 0u32;
    ensures to_integer(x - 1u32) < to_integer(x) by close();
}

theorem successor_within_a_bound(x: uint32) {
    requires x < 4u32;
    ensures to_integer(x + 1u32) <= to_integer(4u32) by close();
}

theorem read_the_other_way_round(x: uint32) {
    requires x > 1u32;
    ensures 1u32 < x by close();
}

theorem difference_decreases(x: uint32, n: uint32) {
    requires x < n;
    ensures to_integer((n - x) - 1u32) < to_integer(n - x) by close();
}

theorem difference_from_a_constant_decreases(x: uint32) {
    requires x < 4u32;
    ensures to_integer((0u32 - x) + 3u32) < to_integer((0u32 - x) + 4u32) by close();
}
```

```expect
pass
```
