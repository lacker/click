# a cell beside a freed allocation is framed across the `free`

The positive twin of
[`a_freed_cell_is_not_framed_by_its_allocation_token.md`](a_freed_cell_is_not_framed_by_its_allocation_token.md).
The proof states separation from the allocation's full byte range before
`free(data)`. The read of `r[0]` crosses the free and keeps its entry value.

```c filename=a_cell_beside_a_freed_allocation_is_framed.c
void dispose_beside(int32* data, int32 n, int32* r) { free(data); }
```

```click
verifying "a_cell_beside_a_freed_allocation_is_framed.c";

resource cell(p: int32*, n: int32) {
    owns allocation(p, n * 4);
    owns p[0..n];
}

void dispose_beside(int32* data, int32 n, int32* r) {
    requires 0 < n;
    requires n < 100;
    consumes cell(data, n);
    views r[0..1];
    requires separate(memory((data as (uint8*))[0..(n * 4)]), memory(r[0..1]));
    ensures r[0] == old(r[0]);
} by {
    unfold(cell(data, n));
    step() by { close(); }
    have separate(statement(0).footprint, memory(r[0])) by {
        close() using {
            separate(memory((data as (uint8*))[0..(n * 4)]), memory(r[0..1]));
        };
    }
    have r[0] == at(statement(0).entry, r[0]) by {
        preserve(memory(r[0]), statement(0));
    }
    step();
    close();
    close(); close(); close();
}
```

```expect
pass
```
