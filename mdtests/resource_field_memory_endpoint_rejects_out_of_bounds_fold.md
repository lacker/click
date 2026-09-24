# Folding a field endpoint outside its bounds is refused

A resource field that selects a memory-range endpoint is still an ordinary
proposed field when the resource is folded, so the body's facts about it must
hold for the proposed value. Here the proposal `capacity + 1` puts the start
past the end: the range `data[capacity + 1..capacity]` asks for no cells, but
the body fact `start <= capacity` fails and the fold is refused. The positive
counterpart is [`resource_field_memory_endpoint.md`](resource_field_memory_endpoint.md).

```c filename=resource_field_memory_endpoint_rejects_out_of_bounds_fold.c
void make(int32* data, int32 capacity) {}
```

```click
resource zero_suffix(data: int32*, capacity: int32) {
    field start: int32;
    owns data[start..capacity];
    fact 0 <= start;
    fact start <= capacity;
}

verifying "resource_field_memory_endpoint_rejects_out_of_bounds_fold.c";

void make(int32* data, int32 capacity) {
    requires 0 <= capacity;
    requires capacity < 1000;
    consumes data[0..capacity];
    produces suffix: zero_suffix(data, capacity);
} by {
    let suffix = fold(zero_suffix(data, capacity), { start: capacity + 1 });
    execute();
}
```

```expect
fail: fact 2 of 2 of the resource body is not established
```
