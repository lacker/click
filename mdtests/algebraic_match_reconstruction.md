# Reconstruction keeps the algebraic match in the goal

```click
spec enum Packet { Empty, Value(int32) }

theorem written(p: Packet) {
    ensures forall (unused: Integer) {
        (match p { Packet::Empty => Packet::Empty, Packet::Value(v) => Packet::Value(v), }) == p
    } by {
        intro();
        close();
    }
}

theorem rewritten(p: Packet, q: Packet) {
    requires q == p;
    ensures (match p { Packet::Empty => Packet::Empty, Packet::Value(v) => Packet::Value(v), }) == q by {
        rewrite(q, p);
        close();
    }
}

spec enum Wide { Word(uint128) }
theorem wide(w: Wide) {
    ensures w == (match w { Wide::Word(bits) => Wide::Word(bits) }) by close();
}
```

```expect
pass
```
