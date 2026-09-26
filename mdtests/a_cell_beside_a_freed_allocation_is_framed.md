# a cell beside a freed allocation is framed across the `free`

The positive twin of
[`a_freed_cell_is_not_framed_by_its_allocation_token.md`](a_freed_cell_is_not_framed_by_its_allocation_token.md).
Separation from the allocation's memory `data[0..n]` is separation by address,
so a read of `r[0]` stated separate from it still crosses `free(data)` and
reaches its entry value.

```c filename=a_cell_beside_a_freed_allocation_is_framed.c
void dispose_beside(int32* data, int32 n, int32* r) { free(data); }
```

```click
verifying "a_cell_beside_a_freed_allocation_is_framed.c";

resource cell(p: int32*, n: int32) {
    contains allocation(p, n * 4);
    owns p[0..n];
}

void dispose_beside(int32* data, int32 n, int32* r) {
    requires 0 < n;
    requires n < 100;
    consumes cell(data, n);
    views r[0..1];
    requires separate(memory(data[0..n]), memory(r[0..1]));
    ensures r[0] == old(r[0]);
} by {
    unfold(cell(data, n));
    execute();
    simp();
}
```

```expect
pass
```
