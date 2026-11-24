# Algebraic matches retain a written or rewritten constructor

```click
spec enum Packet { Empty, Full(int32) }
spec enum Output { NoValue, Value(int32) }

theorem written() {
    ensures forall (unused: Integer) {
        (match Packet::Full(7) {
            Packet::Empty => Output::NoValue,
            Packet::Full(n) => Output::Value(n),
        }) == Output::Value(7)
    } by { intro(); normalize(); }
}

theorem rewritten(p: Packet) {
    requires p == Packet::Full(7);
    ensures (match p {
        Packet::Empty => Output::NoValue,
        Packet::Full(n) => Output::Value(n),
    }) == Output::Value(7) by {
        rewrite(p, Packet::Full(7));
        close();
    }
}

theorem rewritten_symbolic(p: Packet, value: int32) {
    requires p == Packet::Full(value);
    ensures (match p {
        Packet::Empty => Output::NoValue,
        Packet::Full(n) => Output::Value(n),
    }) == Output::Value(value) by {
        rewrite(p, Packet::Full(value));
        close();
    }
}
spec enum WidePacket { Full(uint64) }
spec enum WideOutput { Value(uint64) }

theorem rewritten_wide(p: WidePacket, value: uint64) {
    requires p == WidePacket::Full(value);
    ensures (match p {
        WidePacket::Full(n) => WideOutput::Value(n),
    }) == WideOutput::Value(value) by {
        rewrite(p, WidePacket::Full(value));
        close();
    }
}

spec enum TaggedOutput { Value(uint64, uint64) }

theorem rewritten_tag(p: WidePacket, value: uint64) {
    requires p == WidePacket::Full(value);
    ensures (match p {
        WidePacket::Full(n) => TaggedOutput::Value(n, 7u64),
    }) == TaggedOutput::Value(value, 7u64) by {
        rewrite(p, WidePacket::Full(value));
        close();
    }
}

theorem rewritten_capture(p: WidePacket, value: uint64, other: uint64) {
    requires p == WidePacket::Full(value);
    ensures (match p {
        WidePacket::Full(n) => TaggedOutput::Value(n, other),
    }) == TaggedOutput::Value(value, other) by {
        rewrite(p, WidePacket::Full(value));
        close();
    }
}

spec enum BoolOutput { Value(uint64, Bool) }

theorem rewritten_bool_tag(p: WidePacket, value: uint64) {
    requires p == WidePacket::Full(value);
    ensures (match p {
        WidePacket::Full(n) => BoolOutput::Value(n, true),
    }) == BoolOutput::Value(value, true) by {
        rewrite(p, WidePacket::Full(value));
        close();
    }
}

spec enum BoolPacket { Full(Bool) }
spec enum Flag { Value(Bool) }

theorem rewritten_bool_field(p: BoolPacket, flag: Bool) {
    requires p == BoolPacket::Full(flag);
    ensures (match p {
        BoolPacket::Full(b) => Flag::Value(b),
    }) == Flag::Value(flag) by {
        rewrite(p, BoolPacket::Full(flag));
        close();
    }
}

theorem rewritten_bool_literal(p: BoolPacket) {
    requires p == BoolPacket::Full(true);
    ensures (match p {
        BoolPacket::Full(b) => Flag::Value(b),
    }) == Flag::Value(true) by {
        rewrite(p, BoolPacket::Full(true));
        close();
    }
}

theorem rewritten_bool_capture(p: WidePacket, value: uint64, flag: Bool) {
    requires p == WidePacket::Full(value);
    ensures (match p {
        WidePacket::Full(n) => BoolOutput::Value(n, flag),
    }) == BoolOutput::Value(value, flag) by {
        rewrite(p, WidePacket::Full(value));
        close();
    }
}

spec enum Box { Value(Integer) }
spec enum BoxPacket { Full(Box) }
spec enum BoxOutput { Item(Box) }

theorem rewritten_algebraic_field(p: BoxPacket, value: Box, other: Box) {
    requires p == BoxPacket::Full(value);
    ensures (match p {
        BoxPacket::Full(x) => BoxOutput::Item(x),
    }) == BoxOutput::Item(value) by {
        rewrite(p, BoxPacket::Full(value));
        close();
    }
}

spec enum BoxCapture { Item(uint64, Box) }

theorem rewritten_algebraic_capture(p: WidePacket, value: uint64, captured: Box, other: Box) {
    requires p == WidePacket::Full(value);
    ensures (match p {
        WidePacket::Full(x) => BoxCapture::Item(x, captured),
    }) == BoxCapture::Item(value, captured) by {
        rewrite(p, WidePacket::Full(value));
        close();
    }
}

spec enum Color { Red, Green }
spec enum ColorPacket { Full(Color) }
spec enum ColorOutput { Item(Color) }

theorem rewritten_nullary_field(p: ColorPacket) {
    requires p == ColorPacket::Full(Color::Red);
    ensures (match p {
        ColorPacket::Full(x) => ColorOutput::Item(x),
    }) == ColorOutput::Item(Color::Red) by {
        rewrite(p, ColorPacket::Full(Color::Red));
        close();
    }
}

spec enum ColorTag { Item(uint64, Color) }

theorem rewritten_nullary_tag(p: WidePacket, value: uint64) {
    requires p == WidePacket::Full(value);
    ensures (match p {
        WidePacket::Full(x) => ColorTag::Item(x, Color::Red),
    }) == ColorTag::Item(value, Color::Red) by {
        rewrite(p, WidePacket::Full(value));
        close();
    }
}
```

```expect
pass
```
