# Integer order comparisons retain their matches

```click
spec enum MachinePacket { Empty, Full(int32) }
spec enum IntegerPacket { Empty, Full(Integer) }

theorem machine_written() {
    ensures forall (unused: Integer) {
        (match MachinePacket::Full(7) {
            MachinePacket::Empty => to_integer(0),
            MachinePacket::Full(n) => to_integer(n) + 1,
        }) < 9
    } by { intro(); close(); }
}

theorem machine_rewritten(p: MachinePacket) {
    requires p == MachinePacket::Full(7);
    ensures forall (unused: Integer) {
        (match p {
            MachinePacket::Empty => to_integer(0),
            MachinePacket::Full(n) => to_integer(n) + 1,
        }) < 9
    } by {
        intro();
        rewrite(p, MachinePacket::Full(7));
        close();
    }
}

theorem integer_written() {
    ensures forall (unused: Integer) {
        (match IntegerPacket::Full(7) {
            IntegerPacket::Empty => to_integer(0),
            IntegerPacket::Full(n) => n + 1,
        }) < 9
    } by { intro(); close(); }
}

theorem integer_rewritten(p: IntegerPacket) {
    requires p == IntegerPacket::Full(7);
    ensures forall (unused: Integer) {
        (match p {
            IntegerPacket::Empty => to_integer(0),
            IntegerPacket::Full(n) => n + 1,
        }) < 9
    } by {
        intro();
        rewrite(p, IntegerPacket::Full(7));
        close();
    }
}

theorem integer_written_le() {
    ensures forall (unused: Integer) {
        8 <= (match IntegerPacket::Full(7) {
            IntegerPacket::Empty => to_integer(0),
            IntegerPacket::Full(n) => n + 1,
        })
    } by { intro(); close(); }
}

theorem integer_written_gt() {
    ensures forall (unused: Integer) {
        (match IntegerPacket::Full(7) {
            IntegerPacket::Empty => to_integer(0),
            IntegerPacket::Full(n) => n + 1,
        }) > 7
    } by { intro(); close(); }
}

theorem machine_empty_ge() {
    ensures forall (unused: Integer) {
        (match MachinePacket::Empty {
            MachinePacket::Empty => to_integer(0),
            MachinePacket::Full(n) => to_integer(n) + 1,
        }) >= 0
    } by { intro(); close(); }
}
```

```expect
pass
```
