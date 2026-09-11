# Integer fields in algebraic datatypes

Specification datatypes may carry the mathematical `Integer` type as a
constructor field. The field remains an Integer value for constructor equality
and does not become a machine C integer.

```click
spec enum Box<T> {
    Empty,
    Wrapped(T),
}

theorem integer_field_equality() {
    ensures Box<Integer>::Wrapped(-9223372036854775809)
        == Box<Integer>::Wrapped(-9223372036854775809) by simp;
}

theorem integer_field_match(value: Integer) {
    ensures match Box<Integer>::Wrapped(value) {
        Box::Empty => value,
        Box::Wrapped(inner) => inner,
    } == value by { normalize(); }
}
```

```expect
pass
```
