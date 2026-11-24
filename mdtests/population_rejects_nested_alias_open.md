# An alias cannot reopen an exposed control body

The equal argument identifies the same ordinary control. Nested opening would
duplicate its exclusive counter memory and population authority.

```c filename=resource_population_open.c
struct object {
    int32 refs;
};

int32 object_refcount(struct object* obj, struct object* alias) {
    return obj->refs;
}
```

```click
authorized resource object_ref(obj: struct object*) {}
resource control(obj: struct object*) {
    owns authority(object_ref(obj));
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "resource_population_open.c";

int32 object_refcount(struct object* obj, struct object* alias) {
    owns control(obj);
    requires alias == obj;

    ensures result == count(object_ref(obj));
} by {
    with(control(obj)) {
        with(control(alias)) { }
    }
    close();
}
```

```expect
fail: population body is already open
```
