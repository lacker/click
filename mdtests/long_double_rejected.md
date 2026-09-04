# C0 rejects extended-precision floating-point declarations

`long double` must not be consumed as the supported integer spelling `long`.
It remains outside the explicit binary32/binary64 floating-point boundary and
gets a focused source-positioned diagnostic.

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
fail: unsupported C type `long double`: extended-precision floating-point values are not modeled in C0
```
