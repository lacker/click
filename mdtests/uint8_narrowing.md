# uint8 narrowing with range proof

This checks that assigning or returning an `int32` into `uint8` is accepted
when the current Click facts prove the value is in byte range.

```c filename=uint8_narrowing.c
uint8 narrow_return(int32 x) {
    return x;
}
```

```c filename=uint8_narrow_assign.c
uint8 narrow_assign(int32 x) {
    uint8 y;
    y = x;
    return y;
}
```

```click
verifying "uint8_narrowing.c";
verifying "uint8_narrow_assign.c";

uint8 narrow_return(int32 x) {
    requires x >= 0;
    requires x <= 255;
    ensures narrowed_return: result == x by auto;
}

uint8 narrow_assign(int32 x) {
    requires x >= 0;
    requires x <= 255;
    ensures narrowed_assign: result == x by auto;
}
```

```expect
pass
```
