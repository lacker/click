# A narrow specification cast is always defined

A cast written in a specification is C's conversion: `x as uint16` is `x`
modulo 2^16, as GCC and Clang compute it, so it is defined for every `x`
and needs no range guard. A checked conversion is written `to_uint16(...)`.

```click quick-solve
theorem defined_everywhere(x: int32) {
    ensures defined(x as uint16) by close();
}
```

```expect
pass
```
