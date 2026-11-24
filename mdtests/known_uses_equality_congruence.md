# Available facts use equality closure

The application stays opaque: `known` neither unfolds it nor searches
for a proof. Equal arguments and already admitted result facts suffice.
The operand equality deliberately arrives after the application fact.

```click
function opaque(x: int32) -> int32 { x }
function nested(x: int32) -> int32 { opaque(x) }
function tag(p: int32*) -> int32 { 1 }

theorem rewritten_pointer_argument(p: int32*, q: int32*) {
    requires tag(p) == 1;
    requires p == q;
    ensures tag(p) == 1 by {
        rewrite(p, q);
        close();
    }
}

theorem transported(x: int32, y: int32) {
    requires opaque(x) == 1;
    requires x == y;
    ensures opaque(y) == 1 by close();
}

theorem nested_application(x: int32, y: int32, z: int32) {
    requires nested(opaque(x)) == z;
    requires x == y;
    ensures nested(opaque(y)) == z by close();
}

theorem comparison(x: int32, y: int32, z: int32) {
    requires opaque(x) < z;
    requires x == y;
    ensures opaque(y) < z by close();
}
```

```expect
pass
```
