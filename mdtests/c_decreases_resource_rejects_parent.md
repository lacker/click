# a structural recursive edge cannot reuse its parent

The same folded resource can justify partial correctness of the opaque
self-call, but it is not a strict descendant and therefore proves no
termination.

```c filename=c_decreases_resource_rejects_parent.c
struct node {
    int32 value;
    struct node* next;
};

int32 repeat_node(struct node* node) {
    int32 result;
    result = repeat_node(node);
    return result;
}
```

```click
resource zero_list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        fact node->value == 0;
        contains zero_list(node->next);
    }
}

verifying "c_decreases_resource_rejects_parent.c";

int32 repeat_node(struct node* node) {
    decreases resource zero_list(node);
    requires node != 0;
    views zero_list(node);
    immutable;

    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}
```

```expect
fail: does not pass a direct contained child
```
