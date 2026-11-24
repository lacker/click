# Algebraic-result matches retain their Integer fields

Unfold before rewriting the symbolic scrutinee, so the kernel must reconnect
Integer fields to the arm's generated binders. Concrete inputs, nested arms,
shadowed names, and captured outer values preserve the selected payload.

```click
spec enum Box { Box(Integer) }
spec enum Pair { Pair(Integer, Integer) }
function identity(b: Box) -> Box {
    match b { Box::Box(n) => Box::Box(n), }
}
function nested(b: Box, other: Box) -> Pair {
    match b { Box::Box(n) => match other { Box::Box(m) => Pair::Pair(n, m), }, }
}
function shadow(b: Box, other: Box, n: Integer) -> Box {
    match b { Box::Box(n) => match other { Box::Box(n) => Box::Box(n), }, }
}
function swap(p: Pair) -> Pair {
    match p { Pair::Pair(a, b) => Pair::Pair(b, a), }
}
function capture(b: Box, n: Integer) -> Pair {
    match b { Box::Box(x) => Pair::Pair(x, n), }
}
theorem preserves(b: Box, n: Integer) {
    requires b == Box::Box(n);
    ensures identity(b) == Box::Box(n) by {
        unfold(identity(b));
        rewrite(b, Box::Box(n));
        close();
    }
}
theorem concrete(n: Integer) {
    ensures identity(Box::Box(n)) == Box::Box(n) by {
        unfold(identity(Box::Box(n)));
        close();
    }
}
theorem nested_fields(b: Box, other: Box, n: Integer, m: Integer) {
    requires b == Box::Box(n);
    requires other == Box::Box(m);
    ensures nested(b, other) == Pair::Pair(n, m) by {
        unfold(nested(b, other));
        rewrite(b, Box::Box(n));
        rewrite(other, Box::Box(m));
        close();
    }
}
theorem shadows(b: Box, other: Box, n: Integer, m: Integer, ambient: Integer) {
    requires b == Box::Box(n);
    requires other == Box::Box(m);
    ensures shadow(b, other, ambient) == Box::Box(m) by {
        unfold(shadow(b, other, ambient));
        rewrite(b, Box::Box(n));
        rewrite(other, Box::Box(m));
        close();
    }
}
theorem swaps(p: Pair, a: Integer, b: Integer) {
    requires p == Pair::Pair(a, b);
    ensures swap(p) == Pair::Pair(b, a) by {
        unfold(swap(p));
        rewrite(p, Pair::Pair(a, b));
        close();
    }
}
theorem captures(b: Box, payload: Integer, ambient: Integer) {
    requires b == Box::Box(payload);
    ensures capture(b, ambient) == Pair::Pair(payload, ambient) by {
        unfold(capture(b, ambient));
        rewrite(b, Box::Box(payload));
        close();
    }
}
```

```expect
pass
```
