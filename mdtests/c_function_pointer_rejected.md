# Abstract function-pointer calls require callback contracts

The C signature of `callback` does not specify its behavior. Even though this
project contains one compatible concrete function, verifying `apply`
independently must not infer a callback contract by enumerating the project.
Checked higher-order callback contracts are tracked in
`issues/higher-order-callback-contracts.md`.

```c filename=compare.c
int32 compare(int32 left, int32 right) {
    return left - right;
}
```

```c filename=apply.c
int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {
    int32 result;
    result = callback(left, right);
    return result;
}
```

```c filename=caller.c
int32 caller() {
    int32 result;
    result = apply(&compare, 40, 2);
    return result;
}
```

```click
verifying "compare.c";
verifying "apply.c";
verifying "caller.c";

int32 compare(int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    ensures result == left - right by auto;
}

int32 apply(int32 (*callback)(int32, int32), int32 left, int32 right) {
    requires 0 <= left;
    requires 0 <= right;
    requires right <= left;
    ensures result == left - right by auto;
}

int32 caller() {
    ensures result == 38 by auto;
}
```

```expect
fail: cannot verify call through function pointer `callback`: its behavior has no declared callback contract
```
