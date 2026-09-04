# Whole-struct lvalue loads and copies

Copyable structs can be loaded from a struct pointer as an address-backed value.
Whole-object assignment, embedded-struct assignment, aggregate returns, and
aggregate arguments all reuse the existing typed leaf-copy semantics.

```c filename=struct_aggregate_load_copy.c
struct inner {
    int32 value;
    uint8 flag;
};

struct packet {
    uint8 tag;
    struct inner inner;
    int32 tail;
};

int32 struct_aggregate_load_copy() {
    struct packet* source = malloc(sizeof(struct packet));
    if (source == 0) {
        return 0;
    }
    struct packet* destination = malloc(sizeof(struct packet));
    if (destination == 0) {
        free(source);
        return 0;
    }

    source->tag = 3;
    source->inner.value = 4;
    source->inner.flag = 2;
    source->tail = 5;

    *destination = *source;
    struct packet local;
    local = *destination;
    destination->inner = local.inner;

    free(destination);
    free(source);
    return local.tag + local.inner.value + local.inner.flag + local.tail;
}
```

```click
verifying "struct_aggregate_load_copy.c";

int32 struct_aggregate_load_copy() {
    ensures result == 0 or result == 14 by auto;
}
```

```expect
pass
```
