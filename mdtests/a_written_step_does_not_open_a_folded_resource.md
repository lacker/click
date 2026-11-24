# A written `step()` does not open a folded resource

`step()` executes one C operation and never opens or closes a resource on
its own (design/proof-reuse.md, R4). The store to `p->value` is refused while
`flat(p)` holds it folded, and the refusal names the missing fact. With the
proof omitted, the implicit tail opens `flat(p)` for the same store
([`implicit_tail_opens_a_folded_resource_to_store_through_it.md`](implicit_tail_opens_a_folded_resource_to_store_through_it.md)).

```c filename=a_written_step_does_not_open_a_folded_resource.c
struct cell {
    int32 value;
    int32 other;
};

void bump(struct cell* p) {
    int32 seen = p->other;
    p->value = seen;
}
```

```click
resource flat(p: struct cell*) {
    owns p->value;
    owns p->other;
}

verifying "a_written_step_does_not_open_a_folded_resource.c";

void bump(struct cell* p) {
    owns flat(p);
} by {
    step();
    step();
    step();
    close();
}
```

```expect
fail: missing resource fact `owns p->value`
```
