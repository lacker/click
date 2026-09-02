# pointer-to-pointer out parameters

Pointer-valued cells use the platform pointer width, while the pointers stored
in those cells retain the element width of their own pointees.

```c filename=publish_int32.c
int32 publish_int32(int32** out, int32* source[]) {
    *out = source[0];
    return 0;
}
```

```c filename=publish_uint8.c
int32 publish_uint8(uint8** out, uint8* source[]) {
    *out = source[0];
    return 0;
}
```

```click
verifying "publish_int32.c";

int32 publish_int32(int32** out, int32* source[]) {
    requires loadable(out[0..1]);
    requires loadable(source[0..1]);
    consumes out[0..1];
    consumes source[0..1];

    ensures out[0] == source[0];
    ensures result == 0;
    produces out[0..1] by auto;
    produces source[0..1] by auto;
}

verifying "publish_uint8.c";

int32 publish_uint8(uint8** out, uint8* source[]) {
    requires loadable(out[0..1]);
    requires loadable(source[0..1]);
    consumes out[0..1];
    consumes source[0..1];

    ensures out[0] == source[0];
    ensures result == 0;
    produces out[0..1] by auto;
    produces source[0..1] by auto;
}
```

```expect
pass
```
