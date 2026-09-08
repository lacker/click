# Conditional normalization cites exact facts

```c filename=normalize_using.c
int32 identity(int32 x) { return x; }
```

```click
verifying "normalize_using.c";

int32 identity(int32 x) {
    requires x == 0;
    ensures (if x == 0 { result } else { 7 }) == result;
} by {
    step();
    normalize() using { x == 0; }
}

theorem different<T>(xs: List<T>, ys: List<T>) {
    requires not(xs == ys);
    ensures (if xs == ys { 1 } else { 0 }) == 0 by {
        normalize() using { not(xs == ys); }
    }
}

theorem same<T>(xs: List<T>, ys: List<T>) {
    requires xs == ys;
    ensures (if xs == ys { 7 } else { 0 }) == 7 by {
        normalize() using { xs == ys; }
    }
}

theorem generic_client(xs: List<List<int32>>, ys: List<List<int32>>) {
    requires not(xs == ys);
    ensures (if xs == ys { 1 } else { 0 }) == 0 by {
        apply(different(xs, ys));
    }
}

theorem generic_equal_client(xs: List<List<int32>>, ys: List<List<int32>>) {
    requires xs == ys;
    ensures (if xs == ys { 7 } else { 0 }) == 7 by {
        apply(same(xs, ys));
    }
}

theorem scalar(x: int32, y: int32) {
    requires x < y;
    ensures (if x < y { 1 } else { 2 }) == 1 by {
        normalize() using { x < y; }
    }
}

theorem nested(x: int32, y: int32) {
    requires x < y;
    requires y == 5;
    ensures (if x < y { if y == 5 { 8 } else { 3 } } else { 0 }) == 8 by {
        normalize() using { x < y; y == 5; }
    }
}

theorem empty_evidence(x: int32) {
    ensures x == x by { normalize() using { } }
}
```

```expect
pass
```
