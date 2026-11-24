# Nested matches select constructors stored in earlier pattern binders

```click
spec enum Color { Red, Green }
spec enum Box { Value(Integer) }
spec enum Flag { Empty, Set(Bool) }
spec enum Envelope { Wrap(Box) }
spec enum Stage { Next(Envelope) }

spec enum ColorInput { Hold(Color) }
spec enum BoxInput { Hold(Box) }
spec enum FlagInput { Hold(Flag) }
spec enum EnvelopeInput { Hold(Envelope) }
spec enum PairInput { Hold(Box, Integer) }
spec enum StageInput { Hold(Stage) }

spec enum Chosen { Red, Green }
spec enum NumberResult { Value(Integer) }
spec enum FlagResult { Missing, Value(Bool) }
spec enum BoxResult { Value(Box) }
spec enum PairResult { Value(Integer, Integer) }

theorem select_color(p: ColorInput) {
    requires p == ColorInput::Hold(Color::Red);
    ensures (match p {
        ColorInput::Hold(c) => match c {
            Color::Red => Chosen::Red,
            Color::Green => Chosen::Green,
        },
    }) == Chosen::Red by {
        rewrite(p, ColorInput::Hold(Color::Red));
        close();
    }
}

theorem select_number(p: BoxInput) {
    requires p == BoxInput::Hold(Box::Value(7));
    ensures (match p {
        BoxInput::Hold(b) => match b { Box::Value(x) => NumberResult::Value(x), },
    }) == NumberResult::Value(7) by {
        rewrite(p, BoxInput::Hold(Box::Value(7)));
        close();
    }
}

theorem select_flag(p: FlagInput) {
    requires p == FlagInput::Hold(Flag::Set(true));
    ensures (match p {
        FlagInput::Hold(flag) => match flag {
            Flag::Empty => FlagResult::Missing,
            Flag::Set(x) => FlagResult::Value(x),
        },
    }) == FlagResult::Value(true) by {
        rewrite(p, FlagInput::Hold(Flag::Set(true)));
        close();
    }
}

theorem forward_box(p: EnvelopeInput) {
    requires p == EnvelopeInput::Hold(Envelope::Wrap(Box::Value(7)));
    ensures (match p {
        EnvelopeInput::Hold(e) => match e { Envelope::Wrap(b) => BoxResult::Value(b), },
    }) == BoxResult::Value(Box::Value(7)) by {
        rewrite(p, EnvelopeInput::Hold(Envelope::Wrap(Box::Value(7))));
        close();
    }
}

theorem select_pair(p: PairInput, a: Integer) {
    requires p == PairInput::Hold(Box::Value(7), a);
    ensures (match p {
        PairInput::Hold(b, y) => match b { Box::Value(x) => PairResult::Value(x, y), },
    }) == PairResult::Value(7, a) by {
        rewrite(p, PairInput::Hold(Box::Value(7), a));
        close();
    }
}

theorem select_chain(p: StageInput) {
    requires p == StageInput::Hold(Stage::Next(Envelope::Wrap(Box::Value(9))));
    ensures (match p {
        StageInput::Hold(s) => match s {
            Stage::Next(e) => match e {
                Envelope::Wrap(b) => match b {
                    Box::Value(x) => NumberResult::Value(x),
                },
            },
        },
    }) == NumberResult::Value(9) by {
        rewrite(p, StageInput::Hold(Stage::Next(Envelope::Wrap(Box::Value(9)))));
        close();
    }
}
```

```expect
pass
```
