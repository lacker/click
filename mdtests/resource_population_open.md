# Resource population bodies open without changing their count

A scoped `open` exposes the one body owned by an active population. It does
not consume a unit, and closing the block requires every body resource to be
restored.

```c filename=resource_population_open.c
struct object {
    int32 refs;
};

int32 object_refcount(struct object* obj) {
    return obj->refs;
}
```

```click
resource object_ref(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "resource_population_open.c";

int32 object_refcount(struct object* obj) {
    owns object_ref(obj);

    ensures result == count(object_ref(obj));
} by {
    open(object_ref(obj)) {
        execute();
    }
    simp();
}
```

```expect
pass
```
