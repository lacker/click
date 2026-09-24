# epoch attack 4: a branch join where one arm writes the array

```c filename=array_fact_does_not_survive_a_branch_that_may_write_it.c
void maybe_mark(int32 a[], int32 n, int32 flag) {
    if (flag != 0) {
        a[0] = 1;
    }
}
```

```click
verifying "array_fact_does_not_survive_a_branch_that_may_write_it.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void maybe_mark(int32 a[], int32 n, int32 flag) {
    requires 0 < n;
    consumes a[0..n];
    produces a[0..n];
} by {
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
fail: tactic 3 > have body tactic 1: `simp` failed
```
