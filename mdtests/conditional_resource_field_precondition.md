# field precondition from an active conditional resource

An earlier load-free precondition can activate a folded conditional resource
whose field is needed to lower a later precondition.

```c filename=conditional_resource_field_precondition.c
struct link {
    struct link* next;
};

int32 known_nonempty_next(struct link* node) {
    return 1;
}
```

```click
resource maybe_link(node: struct link*) {
    if node != 0 {
        owns node->next;
    }
}

verifying "conditional_resource_field_precondition.c";

int32 known_nonempty_next(struct link* node) {
    requires node != 0;
    requires node->next != 0;
    owns maybe_link(node);
    immutable;

    ensures result == 1;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
