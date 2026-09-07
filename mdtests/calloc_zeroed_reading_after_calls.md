# a zeroed reading survives a call that cannot reach the allocation

The positive half of `calloc_zeroed_reading_survives_call_rejected.md`. A
callee that states what it wrote lets the caller use that value, and an
allocation outside the callee's footprint keeps reading as zero.

```c filename=fill.c
void fill(int32* p) {
    p[0] = 5;
}
```

```c filename=calloc_zeroed_reading_after_calls.c
int32 written_value() {
    int32* p = calloc(1, sizeof(int32));
    if (p == 0) {
        return 0;
    }
    fill(p);
    int32 first = p[0];
    free(p);
    return first;
}

int32 untouched_allocation() {
    int32* written = calloc(1, sizeof(int32));
    if (written == 0) {
        return 0;
    }
    int32* untouched = calloc(1, sizeof(int32));
    if (untouched == 0) {
        free(written);
        return 0;
    }
    fill(written);
    int32 quiet = untouched[0];
    free(written);
    free(untouched);
    return quiet;
}
```

```click
verifying "fill.c";
verifying "calloc_zeroed_reading_after_calls.c";

void fill(int32* p) {
    owns p[0..1];
    mutable p[0..1];
    ensures p[0] == 5;
}

int32 written_value() {
    ensures result == 5 or result == 0 by auto;
}

int32 untouched_allocation() {
    ensures result == 0 by auto;
}
```

```expect
pass
```
