# Integer pure function calls remain opaque without unfold

```click
function successor(z: Integer) -> Integer {
    z + 1
}

theorem successor_requires_unfold(z: Integer) {
    ensures successor(z) == z + 1 by {
        normalize();
    }
}
```

```expect
fail: goal did not normalize to true
```
