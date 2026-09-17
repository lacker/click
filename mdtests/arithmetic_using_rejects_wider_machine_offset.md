# `arithmetic using` decomposes only the machine successor

`a < b + 1` yields `a <= b` because a wrapped successor makes the strict
premise unsatisfiable. A wider machine offset has satisfiable wrapped cases,
so `a < b + 2` does not yield `a <= b` and the tactic declines it.

```click
theorem strict_offset_two(a: int32, b: int32) {
    requires a < b + 2;
    ensures a <= b by {
        arithmetic() using {
            a < b + 2;
        }
    }
}
```

```expect
fail: current goal does not follow from exactly the listed arithmetic premises
```
