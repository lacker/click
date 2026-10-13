# A function returning `long long` is not a `long (*)(long)` callback

Function types are compatible only when their return and parameter types are
(C11 6.7.6.3p15). `long long (long)` and `long (long)` differ in the return
type's rank alone, so GCC 14 and Clang refuse the uncast conversion as
incompatible pointer types, and Click refuses the callback.

```c filename=main.c
long long twice(long value) {
    return value + value;
}

long apply(long (*callback)(long), long value) {
    return callback(value);
}

long caller(void) {
    return apply(twice, 2);
}
```

```click
verifying "main.c";

int64 twice(int64 value) {
    requires value >= 0 and value <= 100;
    ensures result == value + value by auto;
}

int64 apply(int64 (*callback)(int64), int64 value) {
    ensures true by auto;
}

int64 caller() {
    ensures true by auto;
}
```

```expect
fail: callback signature mismatch
```
