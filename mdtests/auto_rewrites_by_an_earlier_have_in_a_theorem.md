# `auto` rewrites by an earlier `have` in a theorem

A theorem with no C has no execution frontier to record spellings on, yet
`auto` and `simp` cite a premise by its written form. A `have` there is
spelled where the proof stands, as one in a C proof is, so `auto` can rewrite
`black(v)` by `v == Walk::At(d, rest)` and close it by the requirement. The
requirement alone does not do it: `same` has to be unfolded first, which the
rewrite search does not try.

```click
spec enum Walk { At(Integer, Walk), Done }

function black(w: Walk) -> int32 decreases w {
    match w { Walk::At(wd, rest) => black(rest), Walk::Done => 1 }
}

function same(w: Walk) -> Walk {
    w
}

theorem black_through_an_earlier_have(v: Walk, d: Integer, rest: Walk) {
    requires v == same(Walk::At(d, rest));
    requires black(Walk::At(d, rest)) == 1;
    ensures black(v) == 1 by {
        have v == Walk::At(d, rest) by {
            unfold(same(Walk::At(d, rest)));
            rewrite(v == same(Walk::At(d, rest)));
            rewrite(same(Walk::At(d, rest)) == Walk::At(d, rest));
            normalize();
        }
        have black(v) == 1 by auto;
        assumption();
    }
}
```

```expect
pass
```
