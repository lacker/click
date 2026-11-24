# Reject a false Integer successor comparison

Exact arithmetic does not wrap at a machine boundary.

```click quick-solve
theorem integer_successor_false(z: Integer) {
    ensures z + 1 <= z by {
        close();
    }
}
```

```expect
fail: could not establish `(z + 1) <= z`
```
