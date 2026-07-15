# uint8 buffer read

This checks that `uint8[]` parameters use byte-width indexing and can be read
with a matching `read(...)` permission.

```c filename=uint8_buffer_read.c
uint8 read_first_byte(uint8 p[]) {
    return p[0];
}
```

```click
verifying "uint8_buffer_read.c";

uint8 read_first_byte(uint8 p[]) {
    views p[0..1];
    ensures returns_first: result == p[0] by auto;
}
```

```expect
pass
```
