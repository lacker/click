# epoch attack 1: a store into another array parameter

```c filename=array_fact_does_not_survive_a_store_into_a_sibling_array.c
void mark_other(int32 a[], int32 b[], int32 n, int32 j) {
    b[j] = 1;
}
```

```click
verifying "array_fact_does_not_survive_a_store_into_a_sibling_array.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void mark_other(int32 a[], int32 b[], int32 n, int32 j) {
    requires 0 <= j;
    requires j < n;
    requires 0 <= n;
    requires n <= 1073741823;
    requires loadable(a[0..n]);
    requires loadable(b[0..n]);
    consumes b[0..n];
    produces b[0..n];
    views a[0..n];
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
