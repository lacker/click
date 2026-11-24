# Comparing values returned by two constructor matches

```click
spec enum Box { Value(Integer) }
spec enum Flag { Value(Bool) }
spec enum Word { Value(uint64) }
spec enum Pair { Both(Box, Box) }
spec enum Envelope { Hold(Box) }
spec enum FlagEnvelope { Hold(Flag) }
spec enum WordEnvelope { Hold(Word) }
spec enum PairEnvelope { Hold(Pair) }
spec enum Slot { Left(Envelope), Right(Envelope) }
spec enum FlagSlot { Left(FlagEnvelope), Right(FlagEnvelope) }
spec enum WordSlot { Left(WordEnvelope), Right(WordEnvelope) }
spec enum PairSlot { Left(PairEnvelope), Right(PairEnvelope) }
spec enum Choice { Left(Box), Right(Box) }
spec enum ChoiceSlot { Hold(Choice) }
spec enum Number { Hold(Integer) }

function box_of(p: Slot) -> Box {
    match p {
        Slot::Left(e) => match e { Envelope::Hold(b) => b, },
        Slot::Right(e) => match e { Envelope::Hold(b) => b, },
    }
}
function flag_of(p: FlagSlot) -> Flag {
    match p {
        FlagSlot::Left(e) => match e { FlagEnvelope::Hold(b) => b, },
        FlagSlot::Right(e) => match e { FlagEnvelope::Hold(b) => b, },
    }
}
function word_of(p: WordSlot) -> Word {
    match p {
        WordSlot::Left(e) => match e { WordEnvelope::Hold(w) => w, },
        WordSlot::Right(e) => match e { WordEnvelope::Hold(w) => w, },
    }
}
function pair_of(p: PairSlot) -> Pair {
    match p {
        PairSlot::Left(e) => match e { PairEnvelope::Hold(pair) => pair, },
        PairSlot::Right(e) => match e { PairEnvelope::Hold(pair) => pair, },
    }
}
function captured_box(p: Slot, value: Box) -> Box {
    match p { Slot::Left(e) => value, Slot::Right(e) => value, }
}
function rebuilt_box(p: Number) -> Box {
    match p { Number::Hold(value) => Box::Value(value), }
}
function chosen_box(p: ChoiceSlot, other: Box) -> Box {
    match p {
        ChoiceSlot::Hold(c) => match c {
            Choice::Left(b) => other,
            Choice::Right(b) => b,
        },
    }
}
spec enum FlagInput { Hold(Bool) }
spec enum WordInput { Hold(uint64) }
spec enum PairInput { Hold(Integer, Integer) }
function rebuilt_flag(p: FlagInput) -> Flag {
    match p { FlagInput::Hold(a) => Flag::Value(a), }
}
function rebuilt_word(p: WordInput) -> Word {
    match p { WordInput::Hold(a) => Word::Value(a), }
}
function rebuilt_pair(p: PairInput) -> Pair {
    match p { PairInput::Hold(a, b) => Pair::Both(Box::Value(a), Box::Value(b)), }
}
function rebuilt_capture(p: Slot, a: Integer) -> Box {
    match p { Slot::Left(e) => Box::Value(a), Slot::Right(e) => Box::Value(a), }
}
function shadowed_rebuilt_box(p: PairInput) -> Box {
    match p {
        PairInput::Hold(x, other) => match PairInput::Hold(x, other) {
            PairInput::Hold(saved, x) => Box::Value(saved),
        },
    }
}
function capture_or_return(p: Slot, a: Box) -> Box {
    match p {
        Slot::Left(e) => match e { Envelope::Hold(b) => b, },
        Slot::Right(e) => a,
    }
}


theorem equal_literal_boxes(p: Number, q: Slot) {
    requires p == Number::Hold(7);
    requires q == Slot::Right(Envelope::Hold(Box::Value(7)));
    ensures rebuilt_box(p) == box_of(q) by {
        unfold(rebuilt_box(p));
        unfold(box_of(q));
        rewrite(p, Number::Hold(7));
        rewrite(q, Slot::Right(Envelope::Hold(Box::Value(7))));
        close();
    }
}

theorem equal_symbolic_boxes(p: Number, q: Slot, a: Integer, b: Integer) {
    requires p == Number::Hold(a);
    requires q == Slot::Right(Envelope::Hold(Box::Value(a)));
    ensures rebuilt_box(p) == box_of(q) by {
        unfold(rebuilt_box(p));
        unfold(box_of(q));
        rewrite(p, Number::Hold(a));
        rewrite(q, Slot::Right(Envelope::Hold(Box::Value(a))));
        close();
    }
}

theorem equal_opaque_boxes(p: Slot, q: Slot, a: Box, b: Box) {
    requires p == Slot::Left(Envelope::Hold(a));
    requires q == Slot::Right(Envelope::Hold(b));
    ensures captured_box(p, a) == capture_or_return(q, a) by {
        unfold(captured_box(p, a));
        unfold(capture_or_return(q, a));
        rewrite(p, Slot::Left(Envelope::Hold(a)));
        rewrite(q, Slot::Right(Envelope::Hold(b)));
        close();
    }
}

theorem equal_flags(p: FlagInput, q: FlagSlot, a: Bool) {
    requires p == FlagInput::Hold(a);
    requires q == FlagSlot::Right(FlagEnvelope::Hold(Flag::Value(a)));
    ensures rebuilt_flag(p) == flag_of(q) by {
        unfold(rebuilt_flag(p));
        unfold(flag_of(q));
        rewrite(p, FlagInput::Hold(a));
        rewrite(q, FlagSlot::Right(FlagEnvelope::Hold(Flag::Value(a))));
        close();
    }
}

theorem equal_words(p: WordInput, q: WordSlot, a: uint64) {
    requires p == WordInput::Hold(a);
    requires q == WordSlot::Right(WordEnvelope::Hold(Word::Value(a)));
    ensures rebuilt_word(p) == word_of(q) by {
        unfold(rebuilt_word(p));
        unfold(word_of(q));
        rewrite(p, WordInput::Hold(a));
        rewrite(q, WordSlot::Right(WordEnvelope::Hold(Word::Value(a))));
        close();
    }
}

theorem equal_pairs(p: PairInput, q: PairSlot, a: Integer, b: Integer) {
    requires p == PairInput::Hold(a, b);
    requires q == PairSlot::Right(PairEnvelope::Hold(Pair::Both(Box::Value(a), Box::Value(b))));
    ensures rebuilt_pair(p) == pair_of(q) by {
        unfold(rebuilt_pair(p));
        unfold(pair_of(q));
        rewrite(p, PairInput::Hold(a, b));
        rewrite(q, PairSlot::Right(PairEnvelope::Hold(Pair::Both(Box::Value(a), Box::Value(b)))));
        close();
    }
}

theorem capture_equals_binding(p: Slot, q: Slot, a: Box, b: Box) {
    requires p == Slot::Left(Envelope::Hold(b));
    requires q == Slot::Right(Envelope::Hold(a));
    ensures captured_box(p, a) == box_of(q) by {
        unfold(captured_box(p, a));
        unfold(box_of(q));
        rewrite(p, Slot::Left(Envelope::Hold(b)));
        rewrite(q, Slot::Right(Envelope::Hold(a)));
        close();
    }
}

theorem rebuilt_equals_binding(p: Slot, q: Slot, a: Integer) {
    requires p == Slot::Left(Envelope::Hold(Box::Value(0)));
    requires q == Slot::Right(Envelope::Hold(Box::Value(a)));
    ensures rebuilt_capture(p, a) == box_of(q) by {
        unfold(rebuilt_capture(p, a));
        unfold(box_of(q));
        rewrite(p, Slot::Left(Envelope::Hold(Box::Value(0))));
        rewrite(q, Slot::Right(Envelope::Hold(Box::Value(a))));
        close();
    }
}

theorem variant_equals_binding(p: ChoiceSlot, q: Slot, a: Integer, other: Box) {
    requires p == ChoiceSlot::Hold(Choice::Right(Box::Value(a)));
    requires q == Slot::Right(Envelope::Hold(Box::Value(a)));
    ensures chosen_box(p, other) == box_of(q) by {
        unfold(chosen_box(p, other));
        unfold(box_of(q));
        rewrite(p, ChoiceSlot::Hold(Choice::Right(Box::Value(a))));
        rewrite(q, Slot::Right(Envelope::Hold(Box::Value(a))));
        close();
    }
}

theorem shadow_equals_binding(p: PairInput, q: Slot, a: Integer, b: Integer) {
    requires p == PairInput::Hold(a, b);
    requires q == Slot::Right(Envelope::Hold(Box::Value(a)));
    ensures shadowed_rebuilt_box(p) == box_of(q) by {
        unfold(shadowed_rebuilt_box(p));
        unfold(box_of(q));
        rewrite(p, PairInput::Hold(a, b));
        rewrite(q, Slot::Right(Envelope::Hold(Box::Value(a))));
        close();
    }
}
```

```expect
pass
```
