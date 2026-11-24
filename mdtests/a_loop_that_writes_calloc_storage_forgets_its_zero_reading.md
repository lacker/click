# A loop that writes calloc storage forgets the allocation's zero reading

`calloc` storage reads as zero wherever no cached value covers it. The loop
below writes `p[0]` on every iteration, so the loop head has to forget the
allocation's zero reading along with the cells it forgets, exactly as a call
that may write the allocation does
(`calloc_zeroed_reading_survives_call_rejected.md`). It used to forget the
cells only: with no cell left at `p[0]`, the load after the loop fell back on
the zero reading, and the false `ensures result == 0` verified, although `f`
returns 9 whenever `calloc` succeeds.

```c filename=a_loop_that_writes_calloc_storage_forgets_its_zero_reading.c
int32 f() {
    int32* p;
    int32 i;
    int32 first;
    p = calloc(2, sizeof(int32));
    if (p == 0) {
        return 0;
    }
    i = 0;
    while (i < 2) {
        p[0] = 9;
        i = i + 1;
    }
    first = p[0];
    free(p);
    return first;
}
```

```click
verifying "a_loop_that_writes_calloc_storage_forgets_its_zero_reading.c";

int32 f() {
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    branch ensuring {
        fact 1 == 1;
    } {
        true => {
            step();
            close();
        }
        false => {
        }
    }
    step();
    loop {
        decreases 2 - i;
        invariant i >= 0;
        invariant i <= 2;
    }
}
```

```expect
fail: the loop in between may have written it
```
