# known names the missing side

`known()` checks each side modulo known equalities, without searching
for arithmetic consequences. Here
`x <= 10` follows from `x <= 5` but is not itself a fact, so the step is
refused and names that side. `have x <= 10 by solve();` before it repairs it.

```click
theorem known_missing_side(x: int32) {
    requires 0 <= x;
    requires x <= 5;
    ensures 0 <= x and x <= 10 by known();
}
```

```expect
fail: unproved part of the goal: x <= 10
```
