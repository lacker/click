# A current field through an entry-state pointer

```c filename=old_pointer_field_mixed_snapshot.c
struct child {
    int32 payload;
};

struct parent {
    struct child* kid;
};

void observe_parent(struct parent* p) {}
```

```click
verifying "old_pointer_field_mixed_snapshot.c";

void observe_parent(struct parent* p) {
    requires p->kid != 0;
    owns object(p);
    owns p->kid[0..1];
    requires separate(memory(object(p)), memory(p->kid[0..1]));
    ensures old(p->kid)->payload == old(p->kid->payload);
} by {
    execute();
    simp();
}
```

```expect
pass
```
