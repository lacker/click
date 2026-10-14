# A false `bool` claim is refused

`positive(-1)` unfolds to `false`, so the claim `ensures positive(-1);`,
which means `positive(-1) == true`, does not hold.

```click
function positive(x: int32) -> bool { x > 0 }

theorem minus_one_is_positive() {
    ensures positive(-1) by {
        unfold(positive(-1));
        normalize();
    }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
