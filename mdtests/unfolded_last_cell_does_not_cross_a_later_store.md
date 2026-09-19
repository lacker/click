# an unfolded last cell is about the snapshot it was unfolded at

`unfold(icount(a, 0, i + 1)) using { ... }` reads the written cell out of the
snapshot the store produced, so its equation is about that snapshot. A second
store to the same cell makes a new one, and the equation does not carry over.

```c filename=unfolded_last_cell_does_not_cross_a_later_store.c
void mark_twice(int32 a[], int32 n, int32 i) {
    a[i] = 1;
    a[i] = 2;
}
```

```click
verifying "unfolded_last_cell_does_not_cross_a_later_store.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void mark_twice(int32 a[], int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    requires n <= 1073741823;
    consumes a[0..n];
    produces a[0..n];
} by {
    step();
    have 0 <= i by { simp(); }
    have i < 2147483647 by {
        arithmetic() using { i < n; n <= 1073741823; }
    }
    have icount(a, 0, i + 1) == icount(a, 0, i) + 1 by {
        unfold(icount(a, 0, i + 1)) using {
            0 <= i;
            i < 2147483647;
        }
        simp();
    }
    step();
    have icount(a, 0, i + 1) == icount(a, 0, i) + 1 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: tactic 5: `have` failed for `icount(a, 0, (i + 1)) == (icount(a, 0, i) + 1)`
```
