# arithmetic refuses an Integer chain with a link missing

Elimination decides entailment; it does not guess the missing link. Without
`x == y` the goal is not a consequence of the listed equalities, and the
refusal says which fragment was recognized and how each premise was read in it.

```click
theorem unchained_integer_equalities(t: Integer, a: Integer, b: Integer, x: Integer, y: Integer) {
    requires t == a + x;
    requires a == b;
    ensures t == b + y by {
        arithmetic() using {
            t == a + x;
            a == b;
        }
    }
}
```

```expect
fail: read the current goal as an Integer linear claim; no combination of the listed premises proves it
  read as Integer linear claims: 0: `t == (a + x)`, 1: `a == b`
```
