# Function-like macros reject unsupported arity

The first function-like macro slice accepts exactly one parameter and reports
the macro name when an invocation supplies the wrong number of arguments.

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
