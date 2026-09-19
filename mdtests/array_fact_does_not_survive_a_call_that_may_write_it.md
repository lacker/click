# epoch attack 2: a call that may write the array

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
    consumes a[0..n];
    produces a[0..n];
} by {
    have 0 <= 0 by { simp(); }
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    step();
    have icount(a, 0, 0) == 0 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: tactic 3: `have` failed for `icount(a, 0, 0) == 0`
```
