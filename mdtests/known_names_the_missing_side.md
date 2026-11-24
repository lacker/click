# The direct check names the missing side

In checked-only verification, `close()` checks each side modulo available
equalities. Here
`x <= 10` follows from `x <= 5` but is not itself a fact, so the step is
refused and names that side.

```click checked-only
theorem known_missing_side(x: int32) {
    requires 0 <= x;
    requires x <= 5;
    ensures 0 <= x and x <= 10 by close();
}
```

```expect
fail: missing exact fact: x <= 10
```
