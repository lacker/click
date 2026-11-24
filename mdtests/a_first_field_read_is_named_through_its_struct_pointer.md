# A first field read through a struct pointer is named by its field

The first field of a struct sits at the struct pointer's own address, so a
read of `c->count` has the address `c` itself. A diagnostic names that read by
its field, `old(c->count)`, as it names `old(c->limit)`, never `old(*c)`,
which would read the whole struct.

```c filename=a_first_field_read_is_named_through_its_struct_pointer.c
struct counter { int32 count; int32 limit; };

void bump(struct counter* c) {
    c->count = c->count + 1;
}
```

```click
verifying "a_first_field_read_is_named_through_its_struct_pointer.c";

void bump(struct counter* c) {
    owns *c;
    requires 0 <= c->count and c->count < c->limit;
    ensures c->count == old(c->count) + 1;
} by {
    step();
    step();
    have to_integer(old(c->count)) + 1 <= to_integer(old(c->limit)) - 1 by {
        close();
    }
}
```

```expect
fail: goal: to_integer(old(c->count)) + 1 <= to_integer(old(c->limit)) - 1
```
