# uint8 widening to int32

This checks the C integer promotion from the modeled `uint8` type into an
`int32` assignment destination and return value. The existing narrowing rule
must remain checked separately by `uint8_narrowing.md`.

```c filename=uint8_widening.c
int32 widen_return(uint8 value) {
    return value;
}

int32 widen_assign(uint8 value) {
    int32 widened;
    widened = value;
    return widened;
}
```

```click
verifying "uint8_widening.c";

int32 widen_return(uint8 value) {
    ensures return_value: result == value by auto;
}

int32 widen_assign(uint8 value) {
    ensures assigned_value: result == value by auto;
}
```

```expect
pass
```
