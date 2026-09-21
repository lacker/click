# A logical pointer field does not keep its pointee alive

```c filename=aggregate_parameter_pointee_expires.c
struct packet { int32* data; };
void dispose(struct packet input) { free(input.data); }
```

```click
verifying "aggregate_parameter_pointee_expires.c";
resource cell(p: int32*) {
    contains allocation(p, 4);
    owns p[0..1];
}
void dispose(struct packet input) {
    views input.data;
    consumes cell(input.data);
    requires separate(memory(input.data), memory(input.data[0..1]));
    ensures input.data[0] == old(input.data[0]);
} by { unfold(cell(input.data)); execute(); simp(); }
```

```expect
fail: viewable
```
