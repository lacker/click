# `for` initializer declarations are scoped to the loop

A variable declared in a `for` initializer is not visible after the loop.
The parser reports the out-of-scope use instead of lowering it as a surviving
local variable.

```c filename=for_initializer_scope_rejected.c
int32 for_initializer_scope_rejected() {
    int32 total = 0;
    for (int32 i = 0; i < 3; i++) {
        total = total + i;
    }
    return i;
}
```

```click
verifying "for_initializer_scope_rejected.c";

int32 for_initializer_scope_rejected() {
    ensures result == 3;
}
```

```expect
fail: undeclared identifier `i`
```
