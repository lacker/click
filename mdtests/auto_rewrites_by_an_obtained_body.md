# `auto` rewrites by the body `obtain` opened

`obtain` opens an existential, binding its names and assuming its body. The
body is spelled as written, under the names just bound, so `auto` can rewrite
`black(v)` by `v == Walk::At(d, rest)`.

```click
spec enum Walk { At(Integer, Walk), Done }

function black(w: Walk) -> int32 decreases w {
    match w { Walk::At(wd, rest) => black(rest), Walk::Done => 1 }
}

theorem black_through_an_obtained_body(v: Walk, rest: Walk) {
    requires exists (d: Integer) { v == Walk::At(d, rest) };
    ensures exists (e: Integer) { black(v) == black(Walk::At(e, rest)) } by {
        obtain (d: Integer) { v == Walk::At(d, rest) }
        have black(v) == black(Walk::At(d, rest)) by auto;
        witness { e: d };
        assumption();
    }
}
```

```expect
pass
```
