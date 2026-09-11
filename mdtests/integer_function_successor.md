# Integer pure function results stay opaque until unfolded

```click
function successor(z: Integer) -> Integer {
    z + 1
}

theorem successor_unfolds(z: Integer) {
    ensures successor(z) == z + 1 by {
        unfold(successor(z));
        normalize();
    }
}
```

```expect
pass
```
