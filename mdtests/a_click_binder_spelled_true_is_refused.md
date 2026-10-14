# A Click binder spelled `true` is refused

Inside Click, `true` and `false` are the `bool` literals, so a quantifier,
`let`, or Click parameter of that spelling could never be read. It is
refused where it is declared. Only a C name keeps those spellings (see
`a_c_name_spelled_true_keeps_its_c_meaning.md`).

```click
theorem every_value(x: int32) {
    ensures forall (true: int32) { x == x } by { simp(); }
}
```

```expect
fail: `true` is a `bool` literal and cannot name a Click binder
```
