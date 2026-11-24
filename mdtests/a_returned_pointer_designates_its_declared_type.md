# A returned pointer designates its declared return type

A caller may rely on a returned pointer designating an object of the
declared return type, since the callee is held to it. A `long *` result
read through a `long long *` after a `void *` round trip is refused.

```c filename=returns.c
long *as_long(void *v) { return v; }

long long read_back(void *raw) {
    long *q = as_long(raw);
    void *v = q;
    long long *w = v;
    return *w;
}
```

```click
verifying "returns.c";

long *as_long(void *v) {
    ensures address(result) == address(v);
} by {
    step_until(function.exit);
    close();
}

long long read_back(void *raw) {
    ensures true;
}
```

```expect
fail: an object of type `long` accessed through an lvalue of type `long long`
```
