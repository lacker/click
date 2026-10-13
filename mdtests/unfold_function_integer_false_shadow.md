# Unfold cannot substitute an outer Integer into a fresh binder

```click
spec enum NumberBox { Wrap(Integer) }
function number(b: NumberBox) -> Integer { match b { NumberBox::Wrap(v) => v } }
theorem reject_shadowed_false_claim(d: Integer) {
    requires d == 0;
    ensures forall (d: Integer) { number(NumberBox::Wrap(d)) == 0 } by {
        intro(); unfold(number(NumberBox::Wrap(d))); normalize();
    }
}
```

```expect
fail: normalize
```
