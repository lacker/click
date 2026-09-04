# Multi-parameter function-like macros reject wrong arity

A function-like macro invocation must provide one non-empty argument for each
named parameter.

```c filename=main.c
#define ADD(left, right) ((left) + (right))

int32 run() {
    return ADD(1);
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 3;
}
```

```expect
fail: macro `ADD` expects exactly 2 non-empty arguments
```
