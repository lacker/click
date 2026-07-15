# uint8 read resources

This checks that `read(...)` permissions use byte-width indexing for `uint8[]`
parameters.

```c filename=read_second_byte.c
uint8 read_second_byte(uint8 p[]) {
    return p[1];
}
```

```click
verifying "read_second_byte.c";

uint8 read_second_byte(uint8 p[]) {
    requires loadable(p[0..2]);
    views p[1..2];

}
```

```expect
pass
```
