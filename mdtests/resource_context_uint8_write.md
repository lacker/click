# uint8 write resources

This checks that owned memory resources use byte-width indexing for `uint8[]`
stores.

```c filename=write_second_byte.c
uint8 write_second_byte(uint8 p[]) {
    p[1] = 'x';
    return p[1];
}
```

```click
verifying "write_second_byte.c";

uint8 write_second_byte(uint8 p[]) {
    requires loadable(p[0..2]);
    consumes p[1..2];

    produces p[1..2] by auto;
}
```

```expect
pass
```
