# conditional resource proves branchless nullable free

A proof-level case split may expose the appropriate branch of a conditional
resource even when the C implementation has no corresponding `if`.
`free(NULL)` is a no-op in the null case; the nonnull case consumes the
allocation authority and complete object access.

```c filename=conditional_resource_branchless_free.c
struct item {
    int32 value;
};

int32 item_destroy(struct item *item) {
    free(item);
    return 0;
}
```

```c filename=destroy_null.c
struct item {
    int32 value;
};

int32 destroy_null() {
    int32 result = item_destroy(0);
    return result;
}
```

```click
resource owned_item(item: struct item*) {
    if item != 0 {
        contains allocation(item, sizeof(struct item));
        owns object(item);
    }
}

verifying "conditional_resource_branchless_free.c";
verifying "destroy_null.c";

int32 item_destroy(struct item* item) {
    consumes owned_item(item);

    ensures result == 0;
} by {
    if item != 0 {
        unfold(owned_item(item));
        execute();
        simp();
    } else {
        unfold(owned_item(item));
        execute();
        simp();
    }
}

int32 destroy_null() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
