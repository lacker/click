# a recursive resource child proves C termination

A structural `decreases` ranks the hidden finite witness for a guarded recursive
resource. The recursive call must receive a direct contained child; pointer
inequality alone is not the ranking argument.

```c filename=c_decreases_resource_recursive.c
struct node {
    int32 value;
    struct node* next;
};

int32 zero_walk(struct node* node) {
    struct node* next;
    int32 result;
    next = node->next;
    if (next == 0) {
        return node->value;
    }
    result = zero_walk(next);
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

verifying "c_decreases_resource_recursive.c";

int32 zero_walk(struct node* node) {
    decreases zero_list(node);
    requires node != 0;
    views zero_list(node);

    ensures result == 0;
} by {
    observe(zero_list(node));
    if node->next == 0 {
        execute();
        simp();
    } else {
        execute();
        simp();
    }
}
```

```expect
pass
```
