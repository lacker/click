# resource population initialization and finalization

The first produced unit packages the population body. Consuming the last unit
ends the population, allowing its body resources to be returned or destroyed.

```c filename=counted_resource_init.c
struct object {
    int32 refs;
};

struct object* object_init(struct object* obj) {
    obj->refs = 1;
    return obj;
}
```

```c filename=counted_resource_finish.c
struct object {
    int32 refs;
};

void object_finish(struct object* obj) {
    obj->refs = 0;
    free(obj);
}
```

```click
resource object_ref(obj: struct object*) {
    contains allocation(obj, sizeof(struct object));
    owns object(obj);
    fact obj->refs == count(object_ref(obj));
}

verifying "counted_resource_init.c";
verifying "counted_resource_finish.c";

struct object* object_init(struct object* obj) {
    consumes allocation(obj, sizeof(struct object));
    consumes object(obj);
    produces object_ref(obj);

    ensures result == obj;
} by {
    execute();
    fold(object_ref(obj));
    simp();
}

void object_finish(struct object* obj) {
    requires count(object_ref(obj)) == 1;
    consumes object_ref(obj);
} by {
    unfold(object_ref(obj));
    execute();
    simp();
}
```

```expect
pass
```
