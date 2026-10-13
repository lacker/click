# Unfold uses the current Integer binder

```click
spec enum NumberBox { Wrap(Integer) }
function number(b: NumberBox) -> Integer { match b { NumberBox::Wrap(v) => v } }
theorem shadowed_integer(d: Integer) {
    requires d == 0;
    ensures forall (d: Integer) { number(NumberBox::Wrap(d)) == d } by {
        intro(); unfold(number(NumberBox::Wrap(d))); normalize();
    }
}
```

```expect
pass
```
