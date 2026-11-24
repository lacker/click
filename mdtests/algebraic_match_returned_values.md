# Returning algebraic values from selected constructor arms

```click
spec enum Box { Value(Integer) }
spec enum Flag { Value(Bool) }
spec enum Word { Value(uint64) }
spec enum Choice { Left(Box), Right(Box) }
spec enum Pair { Both(Box, Box) }
spec enum Envelope { Hold(Box) }
spec enum Slot { Hold(Envelope) }
spec enum FlagEnvelope { Hold(Flag) }
spec enum FlagSlot { Hold(FlagEnvelope) }
spec enum WordEnvelope { Hold(Word) }
spec enum WordSlot { Hold(WordEnvelope) }
spec enum PairEnvelope { Hold(Pair) }
spec enum PairSlot { Hold(PairEnvelope) }
spec enum ChoiceSlot { Hold(Choice) }
spec enum Number { Hold(Integer) }

function project_returns_literal_box(p: Slot) -> Box {
    match p {
        Slot::Hold(e) => match e { Envelope::Hold(b) => b, },
    }
}

theorem returns_literal_box(p: Slot) {
    requires p == Slot::Hold(Envelope::Hold(Box::Value(7)));
    ensures project_returns_literal_box(p) == Box::Value(7) by {
        unfold(project_returns_literal_box(p));
        rewrite(p, Slot::Hold(Envelope::Hold(Box::Value(7))));
        close();
    }
}

function project_returns_symbolic_box(p: Slot, value: Integer) -> Box {
    match p {
        Slot::Hold(e) => match e { Envelope::Hold(b) => b, },
    }
}

theorem returns_symbolic_box(p: Slot, value: Integer) {
    requires p == Slot::Hold(Envelope::Hold(Box::Value(value)));
    ensures project_returns_symbolic_box(p, value) == Box::Value(value) by {
        unfold(project_returns_symbolic_box(p, value));
        rewrite(p, Slot::Hold(Envelope::Hold(Box::Value(value))));
        close();
    }
}

function project_returns_opaque_box(p: Slot, value: Box, other: Box) -> Box {
    match p {
        Slot::Hold(e) => match e { Envelope::Hold(b) => b, },
    }
}

theorem returns_opaque_box(p: Slot, value: Box, other: Box) {
    requires p == Slot::Hold(Envelope::Hold(value));
    ensures project_returns_opaque_box(p, value, other) == value by {
        unfold(project_returns_opaque_box(p, value, other));
        rewrite(p, Slot::Hold(Envelope::Hold(value)));
        close();
    }
}

function project_returns_capture(p: Envelope, boxed: Box, value: Box, other: Box) -> Box {
    match p { Envelope::Hold(b) => value, }
}

theorem returns_capture(p: Envelope, boxed: Box, value: Box, other: Box) {
    requires p == Envelope::Hold(boxed);
    ensures project_returns_capture(p, boxed, value, other) == value by {
        unfold(project_returns_capture(p, boxed, value, other));
        rewrite(p, Envelope::Hold(boxed));
        close();
    }
}

function project_returns_flag(p: FlagSlot, flag: Bool) -> Flag {
    match p { FlagSlot::Hold(e) => match e { FlagEnvelope::Hold(b) => b, }, }
}

theorem returns_flag(p: FlagSlot, flag: Bool) {
    requires p == FlagSlot::Hold(FlagEnvelope::Hold(Flag::Value(flag)));
    ensures project_returns_flag(p, flag) == Flag::Value(flag) by {
        unfold(project_returns_flag(p, flag));
        rewrite(p, FlagSlot::Hold(FlagEnvelope::Hold(Flag::Value(flag))));
        close();
    }
}

function project_returns_word(p: WordSlot, value: uint64) -> Word {
    match p { WordSlot::Hold(e) => match e { WordEnvelope::Hold(w) => w, }, }
}

theorem returns_word(p: WordSlot, value: uint64) {
    requires p == WordSlot::Hold(WordEnvelope::Hold(Word::Value(value)));
    ensures project_returns_word(p, value) == Word::Value(value) by {
        unfold(project_returns_word(p, value));
        rewrite(p, WordSlot::Hold(WordEnvelope::Hold(Word::Value(value))));
        close();
    }
}

function project_returns_pair(p: PairSlot, first: Integer, second: Integer) -> Pair {
    match p { PairSlot::Hold(e) => match e { PairEnvelope::Hold(p) => p, }, }
}

theorem returns_pair(p: PairSlot, first: Integer, second: Integer) {
    requires p == PairSlot::Hold(PairEnvelope::Hold(Pair::Both(Box::Value(first), Box::Value(second))));
    ensures project_returns_pair(p, first, second) == Pair::Both(Box::Value(first), Box::Value(second)) by {
        unfold(project_returns_pair(p, first, second));
        rewrite(p, PairSlot::Hold(PairEnvelope::Hold(Pair::Both(Box::Value(first), Box::Value(second)))));
        close();
    }
}

function project_returns_selected_variant(p: ChoiceSlot, value: Integer, other: Box) -> Box {
    match p {
        ChoiceSlot::Hold(choice) => match choice {
            Choice::Left(b) => other,
            Choice::Right(b) => b,
        },
    }
}

theorem returns_selected_variant(p: ChoiceSlot, value: Integer, other: Box) {
    requires p == ChoiceSlot::Hold(Choice::Right(Box::Value(value)));
    ensures project_returns_selected_variant(p, value, other) == Box::Value(value) by {
        unfold(project_returns_selected_variant(p, value, other));
        rewrite(p, ChoiceSlot::Hold(Choice::Right(Box::Value(value))));
        close();
    }
}

function project_returns_rebuilt_value(p: Number, value: Integer) -> Box {
    match p { Number::Hold(n) => match Envelope::Hold(Box::Value(n)) { Envelope::Hold(b) => b, }, }
}

theorem returns_rebuilt_value(p: Number, value: Integer) {
    requires p == Number::Hold(value);
    ensures project_returns_rebuilt_value(p, value) == Box::Value(value) by {
        unfold(project_returns_rebuilt_value(p, value));
        rewrite(p, Number::Hold(value));
        close();
    }
}

function project_returns_shadowed_value(p: Pair, first: Integer, second: Integer) -> Box {
    match p { Pair::Both(x, other) => match Pair::Both(x, other) { Pair::Both(saved, x) => saved, }, }
}

theorem returns_shadowed_value(p: Pair, first: Integer, second: Integer) {
    requires p == Pair::Both(Box::Value(first), Box::Value(second));
    ensures project_returns_shadowed_value(p, first, second) == Box::Value(first) by {
        unfold(project_returns_shadowed_value(p, first, second));
        rewrite(p, Pair::Both(Box::Value(first), Box::Value(second)));
        close();
    }
}
```

```expect
pass
```
