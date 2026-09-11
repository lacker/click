# A bare name that is neither an object nor a function is undeclared

C has no implicit declaration for a name used as a value, so a designator that
this translation unit declares neither as an object nor as a function is a
source error rather than an address.

```c filename=c_callback_bare_designator_undeclared.c
int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {
    int32 result;
    result = callback(left, right);
    return result;
}

int32 caller() {
    int32 result;
    result = apply(compare, 40, 2);
    return result;
}
```

```click
verifying "c_callback_bare_designator_undeclared.c";

int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {
    ensures true by auto;
}

int32 caller() {
    ensures true by auto;
}
```

```expect
fail: use of undeclared identifier `compare`
```
