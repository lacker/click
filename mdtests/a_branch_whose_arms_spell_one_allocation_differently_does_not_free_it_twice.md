# A branch whose arms spell one allocation differently does not free it twice

One arm passes the allocation through `same`, whose result is a new spelling
of `p`; the other keeps `p`. The two `free` calls after the `if` then release
one allocation twice, so the function must not verify.

The kernel's memory join keys live allocations by pointer spelling, and could
hold this allocation live under both spellings. It does not: the two arms
abstract to the same successor state, which holds one live allocation, so the
first `free` releases it and the second finds no live allocation to free.

```c filename=spelled_twice.c
int32* same(int32* p) {
    return p;
}

int32 twice(int32* p, int32 flag) {
    int32* s;
    if (flag != 0) {
        s = same(p);
    } else {
        s = p;
    }
    free(s);
    free(p);
    return 0;
}
```

```click
resource allocated(p: int32*) {
    owns allocation(p, 4);
    owns p[0..1];
}

verifying "spelled_twice.c";

int32* same(int32* p) {
    consumes allocated(p);
    produces allocated(result);
    ensures result == p;
} by {
    unfold(allocated(p));
    step_until(function.exit);
    fold(allocated(result));
    close();
}

int32 twice(int32* p, int32 flag) {
    consumes allocated(p);
    ensures result == 0;
} by {
    step();
    branch ensuring {
        owns allocated(s);
    } {
        true => {
            step();
            step();
        }
        false => {
            step();
            unfold(allocated(p));
            fold(allocated(s));
        }
    }
    unfold(allocated(s));
    step();
    step();
    step();
    close();
}
```

```expect
fail: cannot free a pointer that is not a live heap allocation
```
