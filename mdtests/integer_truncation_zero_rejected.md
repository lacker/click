# Multiplication by zero preserves truncation's domain obligation

```click
theorem bad(a: Integer) {
    ensures 0 * truncating_quotient(a, 0) == 0 by close();
}
```

```expect
fail: not established: `false`
```
