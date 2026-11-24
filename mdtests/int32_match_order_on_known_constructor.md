# Signed machine order keeps the match and its comparison

```click
spec enum Packet { Empty, Full(int32) }

theorem written() {
    ensures forall (unused: Integer) {
        (match Packet::Full(-7) {
            Packet::Empty => 0,
            Packet::Full(n) => n,
        }) < 0
    } by { intro(); close(); }
}

theorem rewritten(p: Packet) {
    requires p == Packet::Full(-7);
    ensures forall (unused: Integer) {
        (match p {
            Packet::Empty => 0,
            Packet::Full(n) => n,
        }) < 0
    } by {
        intro();
        rewrite(p, Packet::Full(-7));
        close();
    }
}

theorem right_operand() {
    ensures forall (unused: Integer) {
        0 <= (match Packet::Empty {
            Packet::Empty => 0,
            Packet::Full(n) => n,
        })
    } by { intro(); close(); }
}

theorem both_operands() {
    ensures forall (unused: Integer) {
        (match Packet::Full(7) {
            Packet::Empty => 0,
            Packet::Full(n) => n,
        }) > (match Packet::Empty {
            Packet::Empty => 0,
            Packet::Full(n) => n,
        })
    } by { intro(); close(); }
}

theorem non_strict() {
    ensures forall (unused: Integer) {
        (match Packet::Full(-7) {
            Packet::Empty => 0,
            Packet::Full(n) => n,
        }) >= -7
    } by { intro(); close(); }
}

theorem from_bound(value: int32) {
    requires value < 9;
    ensures (match Packet::Full(value) {
        Packet::Empty => 0,
        Packet::Full(n) => n,
    }) < 9 by close();
}

theorem nested_cast() {
    ensures ((match Packet::Full(7) {
        Packet::Empty => 0,
        Packet::Full(n) => n,
    }) as int64) < (9 as int64) by close();
}

```

```expect
pass
```
