# a refused rewrite says which memory each side reads

`old(a[m])` and `a[m]` read the same address in different states. The
requested equality and current goal use one printer and label map, so their
read widths and address match while their snapshot labels differ. The store
may overwrite `a[m]`; the old equality alone cannot justify the current read.
The diagnostic shows this directly, without an additional display mode.

```c filename=rewrite_names_the_memory_each_side_reads.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "rewrite_names_the_memory_each_side_reads.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires n <= 1073741823;
    requires a[m] == 5;
    consumes a[0..n];
    produces a[0..n];
} by {
    step();
    have a[m] == 5 by {
        rewrite(old(a[m]) == 5);
        assumption();
    }
    execute();
    simp();
}
```

```expect
fail: equality: old(a[m]) == 5
  goal: a[m] == 5
```
