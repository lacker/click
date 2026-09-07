# a call that may write a zeroed allocation ends its zeroed reading

`calloc` storage reads as zero only until something writes it. A callee whose
mutable footprint covers the allocation may have written it, so the caller
cannot keep reading the cells as zero afterwards; that is a claim about the
allocation's contents, invalidated exactly as a stored cell is.

```c filename=fill.c
void fill(int32* p) {
    p[0] = 5;
}
```

```c filename=calloc_zeroed_reading_survives_call_rejected.c
int32 calloc_zeroed_reading_survives_call_rejected() {
    int32* p = calloc(1, sizeof(int32));
    if (p == 0) {
        return 0;
    }
    fill(p);
    int32 first = p[0];
    free(p);
    return first;
}
```

```click
verifying "fill.c";
verifying "calloc_zeroed_reading_survives_call_rejected.c";

void fill(int32* p) {
    owns p[0..1];
    mutable p[0..1];
}

int32 calloc_zeroed_reading_survives_call_rejected() {
    ensures result == 0;
}
```

```expect
fail: unclosed goal
```
