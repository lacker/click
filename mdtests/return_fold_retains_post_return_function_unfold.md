# A returned fold retains a function equation unfolded after return

A standalone function unfold after return proves an equation on that path.
A subsequent `have` and resource fold retain that evidence through final
return certification.

```c filename=pick.c
int32 pick(int32* p, int32 x) {
    *p = x;
    return x;
}
```

```click
spec enum Shape { Leaf, Pair(int32, int32) }
function first(s: Shape) -> int32 {
    match s {
        Shape::Leaf => 0,
        Shape::Pair(a, b) => a,
    }
}
resource Cell(p: int32*) {
    field model: int32;
    owns p[0..1];
    fact p[0] == model;
}
verifying "pick.c";
int32 pick(int32* p, int32 x) {
    consumes p[0..1];
    produces c: Cell(p);
    ensures c.model == first(Shape::Pair(x, 3));
} by {
    step_until(function.exit);
    unfold(first(Shape::Pair(x, 3)));
    have first(Shape::Pair(x, 3)) == x by { close(); }
    let c = fold(Cell(p), { model: x });
    close();
}
```

```expect
pass
```
