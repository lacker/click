# A fixed array view includes the final element

```c filename=array_view.c
struct packet { uint8 bytes[3]; int64 aligned; };
uint8 read(struct packet* p) { return p->bytes[2]; }
```

```click
verifying "array_view.c";
uint8 read(struct packet* p) {
    views p->bytes;
    ensures result == p->bytes[2];
} by { execute(); simp(); }
```

```expect
pass
```
