# counted resource populations finalize independently

Ending one counted population must not consume the body resources belonging to
another population mentioned by the same function.

```c filename=counted_resource_finish_one.c
struct object {
    int32 refs;
};

void object_finish_one(struct object* finished, struct object* kept) {
    finished->refs = 0;
    free(finished);
}
```

```click
counted resource object_ref(obj: struct object*) {
    contains allocation(obj, sizeof(struct object));
    owns object(obj);
    fact obj->refs == count(object_ref(obj));
}

verifying "counted_resource_finish_one.c";

void object_finish_one(struct object* finished, struct object* kept) {
    requires finished != kept;
    requires finished->refs == 1;
    consumes object_ref(finished);
    owns object_ref(kept);
    mutable finished->refs;
} by {
    unfold(object_ref(finished));
    execute();
    frame();
    simp();
}
```

```expect
pass
```
