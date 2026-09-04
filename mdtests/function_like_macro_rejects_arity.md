# Function-like macros reject unsupported arity

A one-parameter function-like macro reports its name when an invocation
supplies the wrong number of arguments.

```c filename=main.c
#define WRAP(value) (value)

int32 run() {
    return WRAP(1, 2);
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 1;
}
```

```expect
fail: macro `WRAP` expects exactly one non-empty argument
```
