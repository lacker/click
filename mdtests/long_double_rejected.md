# C0 rejects extended-precision floating-point values

The target ABI layout is known, but value operations still need an 80-bit
floating-point model. A local declaration receives a focused diagnostic.

```c filename=long_double_rejected.c
int32 long_double_rejected() {
    long double value;
    return 0;
}
```

```click
verifying "long_double_rejected.c";

int32 long_double_rejected() {
    ensures result == 0 by auto;
}
```

```expect
fail: long double value operations need an extended-precision model
```
