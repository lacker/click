# Struct byte-array ranges retain their physical element width

The view and ownership cover adjacent bytes, not adjacent four-byte cells.
The same source spelling works for a global object and a pointer parameter.

```c filename=bytes.c
struct bytes { int32 tag; uint8 data[4]; };
struct bytes global;
uint8 set_global(uint8 value) {
    global.data[2] = value;
    return global.data[1];
}
uint8 set_pointer(struct bytes* p, uint8 value) {
    p->data[2] = value;
    return p->data[1];
}
```

```click
verifying "bytes.c";
uint8 set_global(uint8 value) {
    views global.data[1..2];
    owns global.data[2..3];
    ensures global.data[2] == value by auto;
    ensures result == old(global.data[1]) by auto;
}
uint8 set_pointer(struct bytes* p, uint8 value) {
    views p->data[1..2];
    owns p->data[2..3];
    ensures p->data[2] == value by auto;
    ensures result == old(p->data[1]) by auto;
}
```

```expect
pass
```
