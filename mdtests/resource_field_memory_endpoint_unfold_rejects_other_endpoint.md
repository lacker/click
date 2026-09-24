# Unfolding publishes exactly the folded field's endpoint

Unfolding a resource whose range starts at a field publishes the range from
that field's folded value and from nowhere else. The caller here knows
`suffix.start == 1`, so the unfolded body owns `data[1..capacity]`; a store to
`data[0]` names a cell outside the published range and is refused. The same
proof with the store written to `data[1]` goes through the range and
verifies; [`resource_field_memory_endpoint.md`](resource_field_memory_endpoint.md)
has the positive fixtures.

```c filename=resource_field_memory_endpoint_unfold_rejects_other_endpoint.c
void poke(int32* data, int32 capacity) {
    data[0] = 5;
}
```

```click
resource zero_suffix(data: int32*, capacity: int32) {
    field start: int32;
    owns data[start..capacity];
    fact 0 <= start;
    fact start <= capacity;
}

verifying "resource_field_memory_endpoint_unfold_rejects_other_endpoint.c";

void poke(int32* data, int32 capacity) {
    owns suffix: zero_suffix(data, capacity);
    requires suffix.start == 1;
    requires 1 < capacity;
} by {
    unfold(suffix);
    execute();
    let suffix = fold(zero_suffix(data, capacity), { start: old(suffix.start) });
    simp();
}
```

```expect
fail: missing resource fact `owns data[0..1]`
```
