# `simp` does not chain a scaled bound

The same bound as `have_by_auto_refutes_a_linear_bound.md`, proved with
`simp`. Its `Integer` planner reads listed premises only, so it misses.

```click
theorem simp_misses_scaled_chain(i: Integer, n: Integer, total: Integer) {
    requires i < n;
    requires n <= 1000;
    requires total <= 255 * i;
    ensures total <= 255000 by {
        have total <= 255000 by simp;
        assumption();
    }
}
```

```expect
fail: could not establish `total <= 255000`
```
