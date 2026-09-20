# epoch attack 5: the array's own object is released

`free(a)` releases the very object `icount` reads through, and an allocation
imported from a contract can be a subrange of the caller's memory, so nothing
separates the released allocation from the array. The fact must not carry
across it.

```c filename=array_fact_does_not_survive_freeing_the_array.c
int32 discard(int32 a[], int32 n) {
    free(a);
    return 0;
}
```

```click
resource allocated_int32s(data: int32*, count: int32) {
    contains allocation(data, count * 4);
    owns data[0..count];
    fact data != 0;
}

verifying "array_fact_does_not_survive_freeing_the_array.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

int32 discard(int32 a[], int32 n) {
    requires 1 <= n;
    requires n <= 536870911;
    consumes allocated_int32s(a, n);
} by {
    unfold(allocated_int32s(a, n));
    have 0 <= 0 by { simp(); }
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    execute();
    have icount(a, 0, 0) == 0 by { simp(); }
    simp();
}
```

```expect
fail: a fact about `a` as a whole does not carry across the release of `a`.
```
