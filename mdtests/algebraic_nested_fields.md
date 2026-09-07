# nested algebraic datatype fields

Nested algebraic fields remain symbolic values. This covers both a field whose
declaration names another datatype and a generic field instantiated with an
algebraic type.

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

spec enum Envelope<T> {
    Missing,
    Present(Maybe<T>),
}

spec enum Holder<T> {
    Hold(T),
}

function wrap_nested(value: int32) -> Envelope<int32> {
    Envelope<int32>::Present(Maybe<int32>::Some(value))
}

function flatten_nested(envelope: Envelope<int32>) -> Maybe<int32> {
    match envelope {
        Envelope::Missing => Maybe<int32>::None,
        Envelope::Present(maybe) => maybe,
    }
}

function value_or_nested(envelope: Envelope<int32>, fallback: int32) -> int32 {
    match envelope {
        Envelope::Missing => fallback,
        Envelope::Present(maybe) => match maybe {
            Maybe::None => fallback,
            Maybe::Some(value) => value,
        },
    }
}

function rebuild_nested(envelope: Envelope<int32>) -> Envelope<int32> {
    match envelope {
        Envelope::Missing => Envelope<int32>::Missing,
        Envelope::Present(maybe) => Envelope<int32>::Present(maybe),
    }
}

function hold_maybe(maybe: Maybe<int32>) -> Holder<Maybe<int32>> {
    Holder<Maybe<int32>>::Hold(maybe)
}

function release_maybe(holder: Holder<Maybe<int32>>) -> Maybe<int32> {
    match holder {
        Holder::Hold(maybe) => maybe,
    }
}

theorem nested_constructors_reduce(value: int32, fallback: int32) {
    ensures flatten_nested(wrap_nested(value)) == Maybe<int32>::Some(value) by {
        unfold(flatten_nested(wrap_nested(value)));
        unfold(wrap_nested(value));
        simp();
    }
    ensures value_or_nested(wrap_nested(value), fallback) == value by {
        unfold(value_or_nested(wrap_nested(value), fallback));
        unfold(wrap_nested(value));
        simp();
    }
}

theorem nested_symbolic_reconstruction(envelope: Envelope<int32>) {
    ensures rebuild_nested(envelope) == envelope by {
        unfold(rebuild_nested(envelope));
        simp();
    }
}

theorem algebraic_type_argument_round_trip(maybe: Maybe<int32>) {
    ensures release_maybe(hold_maybe(maybe)) == maybe by {
        unfold(release_maybe(hold_maybe(maybe)));
        unfold(hold_maybe(maybe));
        simp();
    }
}
```

```expect
pass
```
