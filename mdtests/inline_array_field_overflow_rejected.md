# inline array fields do not spill into the following field

```c filename=t.c
struct rec {
    int32 buf[2];
    int32 next;
};

int32 spill(struct rec* r) {
    r->buf[2] = 7;
    return r->next;
}
```

```click
verifying "t.c";

int32 spill(struct rec* r) {
    owns object(r);
    ensures result == 7;
}
```

```expect
fail: array subobject index
```
