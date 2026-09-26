# epoch attack 7: the function calls itself on the same array

A recursive call declares the same footprint the caller holds, so the object the
fact reads through is exactly the object the call may write. The body writes
nothing at all, and that is the point: what the edge carries is the declared
write set, and calling itself is not a way around it. The contract does not
promise to keep `a[0]`, so the claim after the call is not a consequence of
anything the call site may use.

The fact carries content: `icount(a, 0, 1) == 5` comes from
`requires a[0] == 5` through the fold's defining equation, and it reads the
one cell the step may write, so after the step it is false. An empty-range
fact would say nothing here: it is true across any write, and the checked fold
read frame carries it.

```c filename=array_fact_does_not_survive_a_recursive_call_on_the_array.c
void wipe(int32 a[], int32 n) {
    if (n <= 0) {
        return;
    }
    wipe(a, n - 1);
}
```

```click
verifying "array_fact_does_not_survive_a_recursive_call_on_the_array.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void wipe(int32 a[], int32 n) {
    decreases n;
    requires 0 <= n;
    requires a[0] == 5;
    requires n <= 1073741823;
    consumes a[0..1];
    produces a[0..1];
} by {
    have 0 <= 0 by { simp(); }
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    have to_integer(a[0]) == 5 by { simp() using { a[0] == 5; }; }
    have icount(a, 0, 1) == 5 by {
        unfold(icount(a, 0, 1)) using { 0 <= 0; 0 < 2147483647; }
        arithmetic() using { icount(a, 0, 0) == 0; to_integer(a[0]) == 5; }
    }
    execute();
    have icount(a, 0, 1) == 5 by { simp(); }
    simp();
}
```

```expect
fail: a fact about `a` as a whole does not carry across the call. Only a step the kernel proves leaves the whole object alone carries one, and a stated `separate(...)` is not read here.
```
