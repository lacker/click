# Order chains of three facts close

A chain of order facts composes one link at a time. `close()` can select
the links itself, and `close() using` works from the listed premises.
Expansion of the signed chain cites Integer lemmas for the selected links.

```click
theorem signed_by_solve(x: int32, a: int32, b: int32) {
    requires x < a;
    requires a <= b;
    requires b <= 4;
    ensures x < 4 by close();
}

theorem unsigned_by_solve(x: uint32, a: uint32, b: uint32) {
    requires x < a;
    requires a <= b;
    requires b <= 4u32;
    ensures x < 4u32 by close();
}

theorem signed_by_arithmetic(x: int32, a: int32, b: int32) {
    requires x < a;
    requires a <= b;
    requires b <= 4;
    ensures x < 4 by { close() using { x < a; a <= b; b <= 4; }; }
}

theorem unsigned_by_arithmetic(x: uint32, a: uint32, b: uint32) {
    requires x < a;
    requires a <= b;
    requires b <= 4u32;
    ensures x < 4u32 by { close() using { x < a; a <= b; b <= 4u32; }; }
}

theorem four_edges_by_arithmetic(x: int32, a: int32, b: int32, c: int32) {
    requires x < a;
    requires a <= b;
    requires b <= c;
    requires c <= 4;
    ensures x < 4 by { close() using { x < a; a <= b; b <= c; c <= 4; }; }
}
```

```expect
pass
```
