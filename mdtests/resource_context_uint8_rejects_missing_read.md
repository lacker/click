# uint8 read resources reject uncovered byte loads

This checks that a `uint8[]` read permission covers byte indexes, not int32-cell
indexes. Permission for `p[0]` does not cover `p[1]`.

```c filename=read_uncovered_byte.c
uint8 read_uncovered_byte(uint8 p[]) {
    return p[1];
}
```

```click
verifying "read_uncovered_byte.c";

uint8 read_uncovered_byte(uint8 p[]) {
    requires loadable(p[0..2]);
    requires read(p[0..1]);

    ensures read(p[0..1]) by auto;
}
```

```expect
fail: missing resource fact `read(p[1..2])`
```
