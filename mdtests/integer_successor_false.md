# Reject a false Integer successor comparison

Exact arithmetic does not wrap at a machine boundary.

```click
theorem integer_successor_false(z: Integer) {
    ensures z + 1 <= z by {
        simp();
    }
}
```

```expect
fail: simplified proposition was not true: Integer less-or-equal is true
```
