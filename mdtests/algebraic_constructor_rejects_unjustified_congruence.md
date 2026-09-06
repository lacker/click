# constructor congruence requires field equality

The checked congruence rule cannot fabricate equality between unrelated
constructor fields.

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

theorem unjustified_congruence(left: int32, right: int32) {
    ensures Maybe<int32>::Some(left) == Maybe<int32>::Some(right) by simp;
}
```

```expect
fail: `simp` failed
```
