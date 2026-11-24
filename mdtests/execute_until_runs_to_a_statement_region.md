# `step_until` runs to a statement region

`step_until` stops before its target, so a statement region stops it at
the statement's entry, its first atomic region. A call inside a statement
stops it just before that call: here `statement(1).call(f, 1)` is the outer
call of `y = f(f(y));`, after the inner one has returned and before `y` is
assigned.

```c filename=execute_until_statement.c
int32 f(int32 v) { return v + 1; }
int32 probe(int32 x) {
    int32 y = f(x);
    y = f(f(y));
    return y;
}
```

```click
verifying "execute_until_statement.c";

int32 f(int32 v) {
    requires v < 1000;
    ensures result == v + 1;
}

int32 probe(int32 x) {
    requires x < 10;
    ensures result == x + 3;
} by {
    step_until(statement(1).entry);
    have y == x + 1 by close();
    step_until(statement(1).call(f, 1).entry);
    have y == x + 1 by close();
}
```

```expect
pass
```
