# A struct byte-array slice does not authorize writing its neighbor

```c filename=bytes.c
struct bytes { int32 tag; uint8 data[4]; };
void set_pointer(struct bytes* p) {
    p->data[2] = 7;
}
```

```click
verifying "bytes.c";
void set_pointer(struct bytes* p) {
    owns p->data[1..2];
    views p->data[2..3];
    ensures p->data[2] == 7 by auto;
}
```

```expect
fail: missing resource fact
```
