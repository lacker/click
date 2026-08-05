# call-scoped view ends before free

A `views` requirement borrows the caller's owned memory for the duration of
the verified call. The borrow does not remain as a new ghost resource after
the helper returns, so the caller can immediately use its retained allocation
authority and ownership to free the object.

```c filename=read_item.c
struct item {
    int32 value;
};

int32 read_item(struct item* item) {
    return item->value;
}
```

```c filename=heap_scoped_borrow_then_free.c
struct item {
    int32 value;
};

int32 heap_scoped_borrow_then_free() {
    struct item* item = malloc(sizeof(struct item));
    if (item == 0) {
        return -1;
    }
    item->value = 7;
    int32 observed = read_item(item);
    free(item);
    return observed;
}
```

```click
verifying "read_item.c";
verifying "heap_scoped_borrow_then_free.c";

int32 read_item(struct item* item) {
    views object(item);
    immutable;

    ensures result == item->value by auto;
}

int32 heap_scoped_borrow_then_free() {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
pass
```
