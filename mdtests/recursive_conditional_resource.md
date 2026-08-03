# recursive conditional resource

A guarded composite may contain itself. Explicit unfolding exposes one node
and leaves the tail folded.

```c filename=recursive_conditional_resource.c
struct node {
    int32 value;
    struct node* next;
};

int32 list_head(struct node* node) {
    return node->value;
}
```

```c filename=recursive_conditional_empty.c
struct node {
    int32 value;
    struct node* next;
};

int32 empty_list_value(struct node* node) {
    return 0;
}
```

```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        contains list(node->next);
    }
}

verifying "recursive_conditional_resource.c";
verifying "recursive_conditional_empty.c";

int32 list_head(struct node* node) {
    requires node != 0;
    owns list(node);
    immutable;

    ensures result == node->value;
} by {
    unfold(list(node));
    execute();
    fold(list(node));
    frame();
    simp();
}

int32 empty_list_value(struct node* node) {
    requires node == 0;
    owns list(node);
    immutable;

    ensures result == 0;
} by {
    unfold(list(node));
    execute();
    fold(list(node));
    frame();
    simp();
}
```

```expect
pass
```
