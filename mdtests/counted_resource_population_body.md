# counted resource bodies describe the whole population

The body of a counted resource is shared by all units with the same arguments.
`count(...)` names the population size, so a function holding one unit can use
the relationship between the stored reference count and the logical count.

```c filename=counted_resource_population_body.c
struct object {
    int32 refs;
};

int32 object_refcount(struct object* obj) {
    return obj->refs;
}
```

```click
counted resource object_ref(obj: struct object*) {
    owns obj->refs;
    fact obj->refs == count(object_ref(obj));
}

verifying "counted_resource_population_body.c";

int32 object_refcount(struct object* obj) {
    owns object_ref(obj);

    ensures result == count(object_ref(obj));
} by {
    execute();
    simp();
}
```

```expect
pass
```
