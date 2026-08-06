# Smart step carries prior call facts through a later opaque call

A smart modular `step()` names statement-entry facts in its simple
certificate. This lets a fact produced by one opaque call survive a later call
whose disjoint footprint changes the memory snapshot.

```c filename=initialize_box.c
struct box {
    int32 value;
};

int32 initialize_box(struct box* owner, int32 value) {
    owner->value = value;
    return value;
}
```

```c filename=initialize_two_boxes.c
struct box {
    int32 value;
};

int32 initialize_two_boxes(struct box* left, struct box* right, int32 value) {
    int32 ignored;
    ignored = initialize_box(left, value);
    ignored = initialize_box(right, value);
    return left->value;
}
```

```click
resource box(owner: struct box*) {
    owns owner->value;
}

verifying "initialize_box.c";
verifying "initialize_two_boxes.c";

int32 initialize_box(struct box* owner, int32 value) {
    consumes object(owner);
    mutable object(owner);
    produces box(owner);
    ensures result == value;
    ensures owner->value == value;
} by {
    execute();
    fold(box(owner));
    frame();
    simp();
}

int32 initialize_two_boxes(struct box* left, struct box* right, int32 value) {
    requires separate(memory(object(left)), memory(object(right)));
    consumes object(left);
    consumes object(right);
    mutable object(left), object(right);
    produces box(left);
    produces box(right);
    ensures left->value == value;
    ensures right->value == value;
    ensures result == value;
} by {
    execute_until(statement(2));
    step();
    execute();
    frame();
    simp();
}
```

```expect
pass
```
