# A bare designator is checked against the callback signature

Decaying a function designator does not weaken the signature check: passing a
name whose declaration disagrees with the parameter is rejected exactly as
`&name` is.

```c filename=c_callback_bare_designator_signature_mismatch.c
int32 negate(int32 value) {
    return 0 - value;
}

int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {
    int32 result;
    result = callback(left, right);
    return result;
}

int32 caller() {
    int32 result;
    result = apply(negate, 40, 2);
    return result;
}
```

```click
verifying "c_callback_bare_designator_signature_mismatch.c";

int32 negate(int32 value) {
    requires 0 <= value;
    ensures result == 0 - value by auto;
}

int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {
    ensures true by auto;
}

int32 caller() {
    ensures true by auto;
}
```

```expect
fail: callback signature mismatch
```
