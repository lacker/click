# A statement region past the statements as written is refused

A chained region names a statement the function has, an atomic region the
statement has of its own, or a call the statement makes. Past any of them it
is refused with what the statement does have, rather than read as some other
point.

```c filename=statement_path_bounds.c
int32 f(int32 v) { return v + 1; }
int32 probe(int32 x) {
    int32 y = f(x);
    return y;
}
```

```click
verifying "statement_path_bounds.c";

int32 f(int32 v) {
    requires v < 1000;
    ensures result == v + 1;
}

int32 probe(int32 x) {
    requires x < 10;
    ensures result == x + 1;
} by {
    step(); step(); step();
    have at(statement(0).call(f, 1).exit, y) == x + 1 by close();
    close();
}
```

```expect
fail: `statement(0)` calls `f` 1 time(s), so it has no `call(f, 1)`
```
