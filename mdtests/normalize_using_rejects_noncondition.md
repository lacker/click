# Evidence must name a single condition

```click
theorem compound(x: int32, y: int32) {
    requires x == 0 and y == 0;
    ensures x == x by {
        normalize() using { x == 0 and y == 0; }
    }
}
```

```expect
fail: single condition
```
