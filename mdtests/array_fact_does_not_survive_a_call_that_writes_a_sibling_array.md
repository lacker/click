# epoch attack 6: a call whose write set is another array parameter

Every array parameter of one function reaches the same external object, so the
callee's declared write set `b[0..n]` is not shown separate from `a`: the caller
is free to pass one array as both. A structurally separate write set carries a
whole-array fact across a call; this one is not separate.

The fact carries content: `icount(a, 0, 1) == 5` comes from
`requires a[0] == 5` through the fold's defining equation, and it reads the
one cell the step may write, so after the step it is false. An empty-range
fact would say nothing here: it is true across any write, and the checked fold
read frame carries it.

```c filename=array_fact_does_not_survive_a_call_that_writes_a_sibling_array.c
void scribble(int32 b[], int32 n) {
    b[0] = 1;
}

void caller(int32 a[], int32 b[], int32 n) {
    scribble(b, n);
}
```

```click
verifying "array_fact_does_not_survive_a_call_that_writes_a_sibling_array.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void scribble(int32 b[], int32 n) {
    requires 0 < n;
    consumes b[0..n];
    produces b[0..n];
} by {
    execute();
    simp();
}

void caller(int32 a[], int32 b[], int32 n) {
    requires 0 < n;
    requires a[0] == 5;
    consumes b[0..n];
    produces b[0..n];
    views a[0..n];
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
