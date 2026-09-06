# constructor injectivity preserves field positions

An equality of product constructors exposes corresponding fields only. It
does not justify equality between fields at different positions.

```click
spec enum Pair<T> {
    Pair(T, T),
}

theorem wrong_injective_field(first: int32, left: int32, right: int32) {
    requires Pair<int32>::Pair(first, left) == Pair<int32>::Pair(first, right);
    ensures first == left by simp;
}
```

```expect
fail: `simp` failed
```
