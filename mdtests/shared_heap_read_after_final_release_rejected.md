# Reading a child after its final release is refused

The release of the last reference frees the child. A later read of its payload
has no ownership to read through.

```c filename=shared_heap_read_after_final_release_rejected.c
struct child {
    int32 refs;
    int32 payload;
};

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

int32 release_then_read(struct child* obj) {
    child_release(obj);
    return obj->payload;
}
```

```click
import click::integer;

authorized resource child_ref(obj: struct child*) {}

resource child_storage(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
}

resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact to_integer(obj->refs) == to_integer(count(child_ref(obj)));
}

verifying "shared_heap_read_after_final_release_rejected.c";

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(obj->refs) > 1 {
        produces child_control(obj);
    }
    ensures to_integer(count(child_ref(obj))) == to_integer(old(count(child_ref(obj))) - 1);
    ensures to_integer(old(count(child_ref(obj)))) > 1 implies obj->payload == old(obj->payload);
} by {
    unfold(child_control(obj));
    if obj->refs == 1 {
        unfold(child_ref(obj));
        unfold(authority(child_ref(obj)));
        step_until(function.exit);
        close();
    } else {
        unfold(child_ref(obj));
        have 1 < obj->refs by {
            close() using { 1 <= obj->refs; obj->refs != 1; };
        }
        have to_integer(obj->refs - 1) >= 1;
        step();
        step();
        fold(child_control(obj));
        step_until(function.exit);
        close();
    }
}

int32 release_then_read(struct child* obj) {
    requires obj->refs == 1;
    consumes child_control(obj);
    consumes child_ref(obj);
} by {
    step(child_release);
    step();
    close();
}
```

```expect
fail: invalid memory access
```
