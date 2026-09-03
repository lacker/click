# uint32 pointers remain outside the scalar slice

`uint32` is currently modeled as a scalar value only. A pointer declaration
must receive a direct diagnostic instead of being accepted with the wrong
pointee width.

```c filename=uint32_pointer_rejected.c
uint32 uint32_pointer_rejected(uint32 *value) {
    return *value;
}
```

```click
verifying "uint32_pointer_rejected.c";
```

```expect
fail: pointers to uint32 values are not supported yet
```
