# stores to indices ordered by facts keep each other's cells

Three stores to `a[i]`, `a[j]` and `a[k]` under `i < j` and `j < k`. Each
store keeps the cells the earlier ones wrote, because the order walk proves
the indices apart; `i < k` needs both facts. Every index is also bounded by
`n`, as the stores' ownership requires, so the walk that proves an order
also passes through those shared bounds.

The walk reads only the facts filed under each node it reaches. This is the
case that has to keep working when it does: a store at `a[k]` asking
`i < k` reaches `j` through a filed edge and `k` through another.

```c filename=stores_to_ordered_indices_keep_each_other.c
void mark(int32 *a, int32 n, int32 i, int32 j, int32 k) {
    a[i] = 1;
    a[j] = 2;
    a[k] = 3;
}
```

```click
verifying "stores_to_ordered_indices_keep_each_other.c";

void mark(int32 *a, int32 n, int32 i, int32 j, int32 k) {
    requires 0 <= i;
    requires i < j;
    requires j < k;
    requires k < n;
    owns a[0..n];
    ensures a[i] == 1 and a[j] == 2 and a[k] == 3;
} by {
    step_until(function.exit);
    have a[i] == 1 by close();
    have a[j] == 2 by close();
    have a[k] == 3 by close();
    close();
}
```

```expect
pass
```
