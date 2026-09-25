# Disequality is symmetric for int32 values

The point-update proof needs the disequality in the opposite operand order
after comparing the marked index with the range endpoint.

```click
theorem swap_disequality(x: int32, y: int32) {
    requires x != y;
    ensures y != x by {
        simp() using { x != y; }
    }
}
```

```expect
pass
```
