# a freed cell is not framed across its own `free` by its allocation token

A false theorem until the free step stopped reading the allocation *token* as
an address range.

The composite holds `allocation(p, n * 4)` and `owns p[0..n]`, and like every
composite it states its members separate. Those are two different resources,
and saying so says nothing about where their bytes are: the token covers
exactly the memory it sits beside. The free step asked whether the freed
allocation is separate from the cell `data[0]`, and answered yes from the
token's separation from `data[0..n]`, so `data[0]` read after `free(data)` was
framed back to its entry value and `ensures data[0] == old(data[0])` held.

The extent is variable on purpose: with a constant one the entry state seeded a
cell for `data[0]`, and its history already stopped at the free. Only the
allocation's memory, `data[0..n]`, can be separate from a cell by address,
which is what the positive twin
[`a_cell_beside_a_freed_allocation_is_framed.md`](a_cell_beside_a_freed_allocation_is_framed.md)
states.

```c filename=a_freed_cell_is_not_framed_by_its_allocation_token.c
void dispose(int32* data, int32 n) { free(data); }
```

```click
verifying "a_freed_cell_is_not_framed_by_its_allocation_token.c";

resource cell(p: int32*, n: int32) {
    contains allocation(p, n * 4);
    owns p[0..n];
}

void dispose(int32* data, int32 n) {
    requires 0 < n;
    requires n < 100;
    consumes cell(data, n);
    ensures data[0] == old(data[0]);
} by {
    unfold(cell(data, n));
    execute();
    simp();
}
```

```expect
fail: the allocation at `data` was released in between
```
