# Unfold accepts an obtained Integer argument

```click
spec enum Walk { At(Integer, Walk), Done }
function black(w: Walk) -> int32 decreases w {
    match w { Walk::At(wd, rest) => black(rest), Walk::Done => 1 }
}
theorem unfold_an_obtained_integer(rest: Walk) {
    requires exists (d: Integer) { black(Walk::At(d, rest)) == 1 };
    ensures black(rest) == 1 by {
        obtain (d: Integer) { black(Walk::At(d, rest)) == 1 };
        unfold(black(Walk::At(d, rest)));
        assumption();
    }
}
```

```expect
pass
```
