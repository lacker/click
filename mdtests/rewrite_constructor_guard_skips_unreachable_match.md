# Rewriting a constructor guard skips the unreachable match

A known enum constructor decides the conditional before rewriting its selected
branch. The unused arm's binder must neither block that rewrite nor contribute
facts to the selected arm.

```click
spec enum Color { Red, Black }
spec enum Payload { Empty, Value(int32) }
function opaque(x: int32) -> int32 { x + 1 }
function wrapped(c: Color, x: int32, unused: Payload) -> int32 {
    if c == Color::Black { opaque(x) }
    else { match unused { Payload::Empty => 0, Payload::Value(y) => y } }
}
theorem selected_branch(c: Color, x: int32, unused: Payload) {
    requires c == Color::Black;
    requires opaque(x) == 1;
    ensures wrapped(c, x, unused) == 1 by {
        unfold(wrapped(c, x, unused));
        rewrite(c == Color::Black);
        rewrite(opaque(x) == 1);
        normalize();
    }
}
theorem distinct_constructor(c: Color, x: int32) {
    requires c == Color::Red;
    ensures wrapped(c, x, Payload::Empty) == 0 by {
        unfold(wrapped(c, x, Payload::Empty));
        rewrite(c == Color::Red);
        normalize() using { };
    }
}
```

```expect
pass
```
