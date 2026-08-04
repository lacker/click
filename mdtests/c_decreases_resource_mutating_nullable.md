# structural descent permits a nullable recursive destructor

The resource guard may be established by C control flow instead of an entry
precondition. The ordinary contract certifies ownership transfer and `free`;
the structural measure separately certifies that the recursive call receives
the direct contained tail.

```c filename=c_decreases_resource_mutating_nullable.c
struct node {
    int32 value;
    struct node *next;
};

int32 list_destroy(struct node *node) {
    if (node == 0) {
        return 0;
    }
    struct node *next = node->next;
    int32 destroyed = list_destroy(next);
    free(node);
    return 0;
}
```

```click
resource allocated_list(node: struct node*) {
    if node != 0 {
        contains allocation(node, sizeof(struct node));
        owns object(node);
        contains allocated_list(node->next);
    }
}

verifying "c_decreases_resource_mutating_nullable.c";

int32 list_destroy(struct node* node) {
    decreases resource allocated_list(node);
    consumes allocated_list(node);

    ensures result == 0;
} by {
    if node == 0 {
        unfold(allocated_list(node));
        execute();
        simp();
    } else {
        unfold(allocated_list(node));
        execute();
        simp();
    }
}
```

```expect
pass
```
