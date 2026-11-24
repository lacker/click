# Selecting guarded constructor match results

```click
spec enum Switch { Hold(Bool) }
spec enum Decision { Yes, No }
spec enum Box { Value(Integer) }
spec enum Flag { Value(Bool) }
spec enum Word { Value(uint64) }
spec enum BoxInput { Hold(Bool, Box) }
spec enum NumberInput { Hold(Bool, Integer) }
spec enum FlagInput { Hold(Bool, Bool) }
spec enum WordInput { Hold(Bool, uint64) }
spec enum DoubleInput { Hold(Bool, Bool) }

function choose_tag(p: Switch) -> Decision {
    match p {
        Switch::Hold(flag) => if flag { Decision::Yes } else { Decision::No },
    }
}
function choose_literal(p: Switch) -> Box {
    match p {
        Switch::Hold(flag) => if flag { Box::Value(7) } else { Box::Value(8) },
    }
}
function choose_number(p: NumberInput) -> Box {
    match p { NumberInput::Hold(flag, value) => if flag { Box::Value(value) } else { Box::Value(0) }, }
}
function choose_capture(p: BoxInput, value: Box) -> Box {
    match p { BoxInput::Hold(flag, boxed) => if flag { value } else { boxed }, }
}
function choose_flag(p: FlagInput) -> Flag {
    match p { FlagInput::Hold(flag, value) => if flag { Flag::Value(false) } else { Flag::Value(value) }, }
}
function choose_word(p: WordInput) -> Word {
    match p { WordInput::Hold(flag, value) => if flag { Word::Value(value) } else { Word::Value(0u64) }, }
}
function choose_nested(p: BoxInput) -> Box {
    match p {
        BoxInput::Hold(flag, boxed) => if flag {
            match boxed { Box::Value(value) => Box::Value(value), }
        } else {
            Box::Value(0)
        },
    }
}
function choose_twice(p: DoubleInput) -> Box {
    match p {
        DoubleInput::Hold(first, second) => if first {
            if second { Box::Value(1) } else { Box::Value(2) }
        } else {
            Box::Value(3)
        },
    }
}

theorem selected_tag(p: Switch) {
    requires p == Switch::Hold(true);
    ensures choose_tag(p) == Decision::Yes by {
        unfold(choose_tag(p));
        rewrite(p, Switch::Hold(true));
        close();
    }
}

theorem selected_true_literal(p: Switch) {
    requires p == Switch::Hold(true);
    ensures choose_literal(p) == Box::Value(7) by {
        unfold(choose_literal(p));
        rewrite(p, Switch::Hold(true));
        close();
    }
}

theorem selected_false_literal(p: Switch) {
    requires p == Switch::Hold(false);
    ensures choose_literal(p) == Box::Value(8) by {
        unfold(choose_literal(p));
        rewrite(p, Switch::Hold(false));
        close();
    }
}

theorem selected_number(p: NumberInput, a: Integer) {
    requires p == NumberInput::Hold(true, a);
    ensures choose_number(p) == Box::Value(a) by {
        unfold(choose_number(p));
        rewrite(p, NumberInput::Hold(true, a));
        close();
    }
}

theorem selected_capture(p: BoxInput, a: Box, b: Box) {
    requires p == BoxInput::Hold(true, b);
    ensures choose_capture(p, a) == a by {
        unfold(choose_capture(p, a));
        rewrite(p, BoxInput::Hold(true, b));
        close();
    }
}

theorem selected_flag(p: FlagInput, a: Bool) {
    requires p == FlagInput::Hold(false, a);
    ensures choose_flag(p) == Flag::Value(a) by {
        unfold(choose_flag(p));
        rewrite(p, FlagInput::Hold(false, a));
        close();
    }
}

theorem selected_word(p: WordInput, a: uint64) {
    requires p == WordInput::Hold(true, a);
    ensures choose_word(p) == Word::Value(a) by {
        unfold(choose_word(p));
        rewrite(p, WordInput::Hold(true, a));
        close();
    }
}

theorem selected_nested_match(p: BoxInput, a: Integer) {
    requires p == BoxInput::Hold(true, Box::Value(a));
    ensures choose_nested(p) == Box::Value(a) by {
        unfold(choose_nested(p));
        rewrite(p, BoxInput::Hold(true, Box::Value(a)));
        close();
    }
}

theorem selected_second_guard(p: DoubleInput) {
    requires p == DoubleInput::Hold(true, false);
    ensures choose_twice(p) == Box::Value(2) by {
        unfold(choose_twice(p));
        rewrite(p, DoubleInput::Hold(true, false));
        close();
    }
}

theorem selected_both_sides(p: NumberInput, q: Switch) {
    requires p == NumberInput::Hold(true, 7);
    requires q == Switch::Hold(true);
    ensures choose_number(p) == choose_literal(q) by {
        unfold(choose_number(p));
        unfold(choose_literal(q));
        rewrite(p, NumberInput::Hold(true, 7));
        rewrite(q, Switch::Hold(true));
        close();
    }
}
```

```expect
pass
```
