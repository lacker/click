# A branch join forgets a zero reading one arm wrote over

Both arms of the `if (c)` below keep the allocation's `calloc` zero reading,
but the `then` arm also caches the 9 it wrote over the zeros. The join
forgets every cached value nothing preserves, so it has to forget a zero
reading under any value an arm cached: it used to keep the reading because
every arm had it, the load after the join found no cell and read zero, and
the false `ensures result == 0` verified, although `f` returns 9 when `c` is
nonzero.

```c filename=a_branch_that_writes_calloc_storage_forgets_its_zero_reading.c
int32 f(int32 c) {
    int32* p;
    int32 first;
    p = calloc(2, sizeof(int32));
    if (p == 0) {
        return 0;
    }
    if (c) {
        p[0] = 9;
    }
    first = p[0];
    free(p);
    return first;
}
```

```click
verifying "a_branch_that_writes_calloc_storage_forgets_its_zero_reading.c";

int32 f(int32 c) {
    ensures result == 0;
} by {
    step();
    step();
    step();
    branch ensuring {
        fact 1 == 1;
    } then {
        step();
        simp();
    } else {
    }
    branch ensuring {
        fact 1 == 1;
    } then {
        step();
    } else {
    }
    execute();
    simp();
}
```

```expect
fail: left side evaluated to at(statement(9).exit, first), right side evaluated to 0
```
