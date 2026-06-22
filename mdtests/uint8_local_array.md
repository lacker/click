# uint8 local array

This checks that local byte arrays allocate one byte per element and that
indexed stores/loads use byte-width pointer arithmetic.

```c filename=uint8_local_array.c
uint8 local_byte_array() {
    uint8 a[2];
    a[0] = 'x';
    a[1] = 'y';
    return a[1];
}
```

```click
verifying "uint8_local_array.c";

uint8 local_byte_array() {
    ensures returns_second: result == 'y' by auto;
}
```

```expect
pass
```
