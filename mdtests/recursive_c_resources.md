# recursive C calls transfer recursive resources by contract

Each returning recursive call gives the tail resource back. Folding the head
therefore reconstructs the same list owned at entry.

```c filename=list_zero.c
struct node {
    int32 value;
    struct node* next;
};

int32 list_zero(struct node* node) {
    struct node* next;
    int32 result;
    next = node->next;
    if (next == 0) {
        return 0;
    }
    result = list_zero(next);
    return result;
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

verifying "list_zero.c";

int32 list_zero(struct node* node) {
    requires node != 0;
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
