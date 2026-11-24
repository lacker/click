# A store search miss names the store and the fact for an array read

`a[0] = 7; a[j - 1] = 1;` with `1 <= j <= 4` writes `a[0]` twice when
`j == 1`, so `int r = a[0];` is `7` or `1`. The implicit tail spells
`((j - 1) as int32) != 0` before the store and misses it, since it does not
hold when `j == 1`. The store drops the cached `a[0]`, and the claim
`result == 7 or result == 1` is refused: it holds, but only by a case split
on `j == 1`. With `j != 1` the closure makes `1 <= j` strict and keeps the
cell (`a_store_index_bound_and_disequality_keep_a_cached_element.md`).

The refusal names the statement and the fact the search spelled. A proof
that splits on `j == 1` before statement(2) can state it in the other case,
`have ... by close();`, and keep the cell there.

```c filename=a_store_search_miss_names_the_store_and_the_fact_for_an_array_read.c
int read_first(int j) {
    int a[4];
    a[0] = 7;
    a[j - 1] = 1;
    int r = a[0];
    return r;
}
```

```click
verifying "a_store_search_miss_names_the_store_and_the_fact_for_an_array_read.c";

int32 read_first(int32 j) {
    requires 1 <= j;
    requires j <= 4;
    ensures result == 7 or result == 1;
}
```

```expect
fail: statement(2) may have overwritten `a`; it is kept if you state `have ((j - 1) as int32) != 0 by { ... };` before statement(2)
```
