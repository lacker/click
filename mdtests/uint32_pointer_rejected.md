# uint32 pointers retain their four-byte element width

`uint32` pointers use the same four-byte element width as their scalar
representation, including resource-backed loads.

```c filename=uint32_pointer_rejected.c
uint32 uint32_pointer_rejected(uint32 *value) {
    return *value;
}
```

```click
verifying "uint32_pointer_rejected.c";

uint32 uint32_pointer_rejected(uint32* value) {
    requires loadable(value[0..1]);
    views value[0..1];
    ensures result == value[0] by auto;
}
```

```expect
pass
```
