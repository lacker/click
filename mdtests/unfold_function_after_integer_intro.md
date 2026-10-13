# Unfold accepts an introduced Integer argument

```click
spec enum Walk { At(Integer, Walk), Done }
function black(w: Walk) -> int32 decreases w {
    match w { Walk::At(wd, rest) => black(rest), Walk::Done => 1 }
}
theorem unfold_an_introduced_integer(rest: Walk) {
    requires black(rest) == 1;
    ensures forall (d: Integer) { black(Walk::At(d, rest)) == 1 } by {
        intro();
        unfold(black(Walk::At(d, rest)));
        assumption();
    }
}
theorem unfold_a_parameter(d: Integer, rest: Walk) {
    requires black(rest) == 1;
    ensures black(Walk::At(d, rest)) == 1 by {
        unfold(black(Walk::At(d, rest)));
        assumption();
    }
}
```

```expect
pass
```
