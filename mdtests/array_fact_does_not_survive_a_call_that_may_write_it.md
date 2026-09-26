# epoch attack 2: a call that may write the array

`scribble` writes `a[0]`, and its declared write set `a[0..n]` says it may.

The fact carries content: `icount(a, 0, 1) == 5` comes from
`requires a[0] == 5` through the fold's defining equation, and it reads the
one cell the step may write, so after the step it is false. An empty-range
fact would say nothing here: it is true across any write, and the checked fold
read frame carries it.

```c filename=array_fact_does_not_survive_a_call_that_may_write_it.c
void scribble(int32 a[], int32 n) {
    a[0] = 1;
}

void caller(int32 a[], int32 n) {
    scribble(a, n);
}
```

```click
verifying "array_fact_does_not_survive_a_call_that_may_write_it.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void scribble(int32 a[], int32 n) {
    requires 0 < n;
    consumes a[0..n];
    produces a[0..n];
} by {
    execute();
    simp();
}

void caller(int32 a[], int32 n) {
    requires 0 < n;
    requires a[0] == 5;
    consumes a[0..n];
    produces a[0..n];
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
    step();
    have icount(a, 0, 1) == 5 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: a fact about `a` as a whole does not carry across the call. Only a step the kernel proves leaves the whole object alone carries one, and a stated `separate(...)` is not read here.
```
