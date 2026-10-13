# Unfold refuses an unbound Integer argument

```click
spec enum NumberBox { Wrap(Integer) }
function number(b: NumberBox) -> Integer { match b { NumberBox::Wrap(v) => v } }
theorem reject_unbound_integer() {
    ensures 1 == 1 by { unfold(number(NumberBox::Wrap(d))); normalize(); }
}
```

```expect
fail: Integer
```
