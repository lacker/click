# One C source may contain a prototype and multiple definitions

The verifier collects every function definition in a source file. A caller
may be defined before its callee when a compatible prototype appears first.

```c filename=multiple_functions.c
int32 increment(int32 value);

int32 caller(int32 value) {
    int32 result;
    result = increment(value);
    return result;
}

int32 increment(int32 value) {
    return value + 1;
}
```

```click
verifying "multiple_functions.c";

int32 caller(int32 value) {
    requires value < 2147483647;
    ensures result == value + 1;
}

int32 increment(int32 value) {
    requires value < 2147483647;
    ensures result == value + 1;
}
```

```expect
pass
```
