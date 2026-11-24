# Constructor matches with compound result fields

```click
spec enum Box { Value(Integer) }
spec enum Pair { Both(Box, Box) }

spec enum InputForwarded { Value(Box) }
spec enum ResultForwarded { Item(Box) }
theorem forwarded(p: InputForwarded, value: Integer, other: Integer) {
    requires p == InputForwarded::Value(Box::Value(7));
    ensures (match p {
        InputForwarded::Value(x) => ResultForwarded::Item(x),
    }) == ResultForwarded::Item(Box::Value(7)) by {
        rewrite(p, InputForwarded::Value(Box::Value(7)));
        close();
    }
}

spec enum InputWrapped { Value(Integer) }
spec enum ResultWrapped { Item(Box) }
theorem wrapped(p: InputWrapped, value: Integer, other: Integer) {
    requires p == InputWrapped::Value(value);
    ensures (match p {
        InputWrapped::Value(x) => ResultWrapped::Item(Box::Value(x)),
    }) == ResultWrapped::Item(Box::Value(value)) by {
        rewrite(p, InputWrapped::Value(value));
        close();
    }
}

spec enum InputCaptured { Value(Integer) }
spec enum ResultCaptured { Tagged(Integer, Box) }
theorem captured(p: InputCaptured, value: Integer, other: Integer) {
    requires p == InputCaptured::Value(value);
    ensures (match p {
        InputCaptured::Value(x) => ResultCaptured::Tagged(x, Box::Value(other)),
    }) == ResultCaptured::Tagged(value, Box::Value(other)) by {
        rewrite(p, InputCaptured::Value(value));
        close();
    }
}

spec enum InputTagged { Value(Integer) }
spec enum ResultTagged { Tagged(Integer, Box) }
theorem tagged(p: InputTagged, value: Integer, other: Integer) {
    requires p == InputTagged::Value(value);
    ensures (match p {
        InputTagged::Value(x) => ResultTagged::Tagged(x, Box::Value(7)),
    }) == ResultTagged::Tagged(value, Box::Value(7)) by {
        rewrite(p, InputTagged::Value(value));
        close();
    }
}

spec enum InputMixed { Value(Integer) }
spec enum ResultMixed { Item(Pair) }
theorem mixed(p: InputMixed, value: Integer, other: Integer) {
    requires p == InputMixed::Value(value);
    ensures (match p {
        InputMixed::Value(x) => ResultMixed::Item(Pair::Both(Box::Value(x), Box::Value(other))),
    }) == ResultMixed::Item(Pair::Both(Box::Value(value), Box::Value(other))) by {
        rewrite(p, InputMixed::Value(value));
        close();
    }
}
```

```expect
pass
```
