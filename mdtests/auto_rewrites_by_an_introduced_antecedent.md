# `auto` rewrites by an antecedent `intro` introduced

`intro` on an implication assumes its antecedent. The antecedent is spelled
as the goal wrote it, as a `have` is, so `auto` can rewrite `black(v)` by
`v == Walk::At(d, rest)` and close it by the requirement.

```click
spec enum Walk { At(Integer, Walk), Done }

function black(w: Walk) -> int32 decreases w {
    match w { Walk::At(wd, rest) => black(rest), Walk::Done => 1 }
}

theorem black_under_an_antecedent(v: Walk, d: Integer, rest: Walk) {
    requires black(Walk::At(d, rest)) == 1;
    ensures v == Walk::At(d, rest) implies black(v) == 1 by {
        intro();
        have black(v) == 1 by auto;
        assumption();
    }
}
```

```expect
pass
```
