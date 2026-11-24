# known closes a mirrored disequality

`x != y` and `y != x` are one claim, for C integers and for `Integer`, as
`x == y` and `y == x` are.

```c filename=known_closes_a_mirrored_disequality.c
void unused(void) {}
```

```click
verifying "known_closes_a_mirrored_disequality.c";

theorem machine(x: int32, y: int32) {
    requires x != y;
    ensures y != x by { close(); }
}

theorem exact(x: int32, y: int32) {
    requires to_integer(x) != to_integer(y);
    ensures to_integer(y) != to_integer(x) by { close(); }
}
```

```expect
pass
```
