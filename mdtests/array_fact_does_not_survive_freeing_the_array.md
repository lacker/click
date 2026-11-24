# epoch attack 5: the array's own object is released

`free(a)` releases the very object `icount` reads through, and an allocation
imported from a contract can be a subrange of the caller's memory, so nothing
separates the released allocation from the array. The fact must not carry
across it.

This checks a nonempty fold: an empty fold can be freshly proved after a
release without carrying any old memory contents.

```c filename=array_fact_does_not_survive_freeing_the_array.c
int32 discard(int32 a[], int32 n) {
    free(a);
    return 0;
}
```

```click
resource allocated_int32s(data: int32*, count: int32) {
    owns allocation(data, count * 4);
    owns data[0..count];
    fact data != 0;
}

verifying "array_fact_does_not_survive_freeing_the_array.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

int32 discard(int32 a[], int32 n) {
    requires a[0] == 5;
    requires 1 <= n;
    requires n <= 536870911;
    consumes allocated_int32s(a, n);
} by {
    unfold(allocated_int32s(a, n));
    have 0 <= 0;
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0));
        close();
    }
    have to_integer(a[0]) == 5 by { close() using { a[0] == 5; }; }
    have icount(a, 0, 1) == 5 by {
        unfold(icount(a, 0, 1));
        close() using { icount(a, 0, 0) == 0; to_integer(a[0]) == 5; };
    }
    step_until(function.exit);
    have icount(a, 0, 1) == 5;
    close();
}
```

```expect
fail: a fact about `a` as a whole does not carry across the release of `a`.
```
