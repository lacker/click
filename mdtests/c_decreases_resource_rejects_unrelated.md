# an unrelated resource is not a structural descendant

Even a different nonnull pointer and a same-named resource at that pointer do
not establish ancestry from the declared measure.

```c filename=c_decreases_resource_rejects_unrelated.c
struct node {
    int32 value;
    struct node* next;
};

int32 swap_repeat(struct node* node, struct node* other) {
    int32 result;
    result = swap_repeat(other, node);
    return result;
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

verifying "c_decreases_resource_rejects_unrelated.c";

int32 swap_repeat(struct node* node, struct node* other) {
    decreases resource zero_list(node);
    requires node != 0;
    requires other != 0;
    requires node != other;
    views zero_list(node);
    views zero_list(other);
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
