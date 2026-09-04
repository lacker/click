# Aggregate field views survive a helper call

An enclosing owned allocation can justify a read-only helper contract that
borrows a mixed-width embedded aggregate. The caller retains ownership while
the callee receives the typed leaf views needed by its field access.

```c filename=struct_aggregate_helper_view.c
struct inner { int32 value; uint8 flag; };
struct packet { uint8 tag; struct inner inner; int32 tail; };

uint8 inspect_packet(struct packet* source) {
    return source->inner.flag;
}

int32 run_inspect() {
    struct packet* source = malloc(sizeof(struct packet));
    if (source == 0) {
        return 0;
    }
    source->inner.flag = 2;
    uint8 result = inspect_packet(source);
    free(source);
    return result;
}
```

```click
verifying "struct_aggregate_helper_view.c";

uint8 inspect_packet(struct packet* source) {
    views source->inner;
    ensures result == source->inner.flag;
} by {
    execute();
    simp();
}

int32 run_inspect() {
    ensures result == 0 or result == 2 by auto;
}
```

```expect
pass
```
