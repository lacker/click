# C for loop declaration rejection

This documents the first `for` slice boundary: C0 lowers assignment-style
`for` loops to `while`, but does not support declarations inside the `for`
initializer yet.

```c filename=for_loop_rejects_declaration.c
int32 for_loop_rejects_declaration() {
    int32 total;
    total = 0;
    for (int32 i; i < 3; i = i + 1) {
        total = total + i;
    }
    return total;
}
```

```click
verifying "for_loop_rejects_declaration.c";

int32 for_loop_rejects_declaration() {
    ensures result == 3 by auto;
}
```

```expect
fail: for-loop declarations require an initializer
```
