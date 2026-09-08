# Congruence does not grant the equality it uses

```click
theorem no_equality(xs: List<int32>, ys: List<int32>, value: int32) {
    ensures list_contains(xs, value) == list_contains(ys, value) by {
        rewrite(xs == ys);
        normalize();
    }
}
```

```expect
fail: exact available fact
```
