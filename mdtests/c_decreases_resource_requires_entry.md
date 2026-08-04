# a structural measure must name an entry resource

```c filename=c_decreases_resource_requires_entry.c
struct node {
    int32 value;
    struct node* next;
};

int32 unmeasured_walk(struct node* node) {
    return 0;
}
```

```click
resource zero_list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        contains zero_list(node->next);
    }
}

verifying "c_decreases_resource_requires_entry.c";

int32 unmeasured_walk(struct node* node) {
    decreases resource zero_list(node);
    ensures result == 0 by auto;
}
```

```expect
fail: must exactly match an owned or viewed entry resource
```
