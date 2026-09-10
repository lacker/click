# Integer fields in algebraic datatypes

Specification datatypes may carry the mathematical `Integer` type as a
constructor field. The field remains an Integer value for constructor equality
and does not become a machine C integer.

```c filename=algebraic_integer_fields.c
int32 identity(int32 value) {
    return value;
}
```

```click
verifying "algebraic_integer_fields.c";

spec enum Box<T> {
    Empty,
    Wrapped(T),
}

theorem integer_field_equality(value: Integer) {
    ensures Box<Integer>::Wrapped(value)
        == Box<Integer>::Wrapped(value) by simp;
}

theorem integer_field_match(value: Integer) {
    ensures match Box<Integer>::Wrapped(value) {
        Box::Empty => value,
        Box::Wrapped(inner) => inner,
    } == value by { normalize(); assumption(); }
}




```

```expect
pass
```
