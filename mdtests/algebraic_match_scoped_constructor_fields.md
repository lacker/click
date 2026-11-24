# Compound pattern fields retain the scope in which they were written

```click
spec enum N { Value(Integer) }
spec enum B { Value(Bool) }
spec enum W { Value(uint64) }
spec enum P { Pair(N, N) }
spec enum Choice { Left(N), Right(N) }
spec enum NumberInput { Hold(Integer) }
spec enum PairInput { Hold(Integer, Integer) }
spec enum BoxInput { Hold(N) }
spec enum BoolInput { Hold(B) }
spec enum WordInput { Hold(W) }
spec enum NestedInput { Hold(P) }
spec enum ChoiceInput { Hold(Choice) }
spec enum NumberOutput { Item(Integer) }
spec enum BooleanOutput { Item(B) }
spec enum WordOutput { Item(W) }
spec enum BoxOutput { Item(N) }
spec enum PairOutput { Item(P) }
spec enum NumberPairOutput { Item(Integer, Integer) }

theorem symbolic_integer(p: BoxInput, a: Integer, b: Integer) {
    requires p == BoxInput::Hold(N::Value(a));
    ensures (match p {
        BoxInput::Hold(x) => BoxOutput::Item(x),
    }) == BoxOutput::Item(N::Value(a)) by {
        rewrite(p, BoxInput::Hold(N::Value(a)));
        close();
    }
}

theorem symbolic_bool(p: BoolInput, a: Bool) {
    requires p == BoolInput::Hold(B::Value(a));
    ensures (match p {
        BoolInput::Hold(x) => BooleanOutput::Item(x),
    }) == BooleanOutput::Item(B::Value(a)) by {
        rewrite(p, BoolInput::Hold(B::Value(a)));
        close();
    }
}

theorem symbolic_word(p: WordInput, a: uint64) {
    requires p == WordInput::Hold(W::Value(a));
    ensures (match p {
        WordInput::Hold(x) => WordOutput::Item(x),
    }) == WordOutput::Item(W::Value(a)) by {
        rewrite(p, WordInput::Hold(W::Value(a)));
        close();
    }
}

theorem mixed_payload(p: NestedInput, a: Integer) {
    requires p == NestedInput::Hold(P::Pair(N::Value(a), N::Value(7)));
    ensures (match p {
        NestedInput::Hold(pair) => PairOutput::Item(pair),
    }) == PairOutput::Item(P::Pair(N::Value(a), N::Value(7))) by {
        rewrite(p, NestedInput::Hold(P::Pair(N::Value(a), N::Value(7))));
        close();
    }
}

theorem select_symbolic(p: BoxInput, a: Integer, b: Integer) {
    requires p == BoxInput::Hold(N::Value(a));
    ensures (match p {
        BoxInput::Hold(box) => match box { N::Value(x) => NumberOutput::Item(x), },
    }) == NumberOutput::Item(a) by {
        rewrite(p, BoxInput::Hold(N::Value(a)));
        close();
    }
}

theorem construct_from_outer_binding(p: NumberInput, a: Integer) {
    requires p == NumberInput::Hold(a);
    ensures (match p {
        NumberInput::Hold(x) => match BoxInput::Hold(N::Value(x)) { BoxInput::Hold(y) => BoxOutput::Item(y), },
    }) == BoxOutput::Item(N::Value(a)) by {
        rewrite(p, NumberInput::Hold(a));
        close();
    }
}

theorem shadow_outer_binding(p: NumberInput, a: Integer, b: Integer) {
    requires p == NumberInput::Hold(a);
    ensures (match p {
        NumberInput::Hold(x) => match P::Pair(N::Value(x), N::Value(b)) { P::Pair(saved, x) => BoxOutput::Item(saved), },
    }) == BoxOutput::Item(N::Value(a)) by {
        rewrite(p, NumberInput::Hold(a));
        close();
    }
}

theorem relay_compound(p: BoxInput, a: Integer) {
    requires p == BoxInput::Hold(N::Value(a));
    ensures (match p {
        BoxInput::Hold(box) => match BoxInput::Hold(box) {
            BoxInput::Hold(copy) => match copy {
                N::Value(x) => BoxOutput::Item(N::Value(x)),
            },
        },
    }) == BoxOutput::Item(N::Value(a)) by {
        rewrite(p, BoxInput::Hold(N::Value(a)));
        close();
    }
}

theorem select_variant(p: ChoiceInput, a: Integer) {
    requires p == ChoiceInput::Hold(Choice::Left(N::Value(a)));
    ensures (match p {
        ChoiceInput::Hold(choice) => match choice {
            Choice::Left(box) => NumberPairOutput::Item(1, a),
            Choice::Right(box) => NumberPairOutput::Item(2, a),
        },
    }) == NumberPairOutput::Item(1, a) by {
        rewrite(p, ChoiceInput::Hold(Choice::Left(N::Value(a))));
        close();
    }
}

theorem select_two_children(p: PairInput, a: Integer, b: Integer) {
    requires p == PairInput::Hold(a, b);
    ensures (match p {
        PairInput::Hold(x, y) => match P::Pair(N::Value(x), N::Value(y)) {
            P::Pair(left, right) => match left {
                N::Value(i) => match right {
                    N::Value(j) => NumberPairOutput::Item(j, i),
                },
            },
        },
    }) == NumberPairOutput::Item(b, a) by {
        rewrite(p, PairInput::Hold(a, b));
        close();
    }
}
```

```expect
pass
```
