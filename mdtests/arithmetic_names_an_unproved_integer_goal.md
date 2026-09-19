# arithmetic says how it read an unproved Integer goal

An `Integer` linear goal never reaches the signed int32 planner, so reporting
that planner's precondition for it named a fragment the goal is not in. The
refusal names the fragment it did recognize and how each listed premise was
read inside it: a premise outside the fragment is skipped rather than refused,
so a reader whose evidence never entered the planner has to be told which
premises did.

```click
theorem unentailed_integer_successor(x: Integer, y: Integer, z: Integer, n: int32) {
    requires x == y + 1;
    requires 0 < n;
    ensures x == z + 1 by {
        arithmetic() using {
            x == y + 1;
            0 < n;
        }
    }
}
```

```expect
fail: read the current goal as an Integer linear claim; no combination of the listed premises proves it
  read as Integer linear claims: 0: `x == (y + 1)`
  skipped, not an Integer linear claim: 1: `0 < n`
```
