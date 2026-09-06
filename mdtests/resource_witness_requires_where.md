# A resource witness needs a `where` clause

```c filename=resource_witness_requires_where.c
struct node {
    int32 value;
    unsigned long word;
};

int32 unused(struct node* node) {
    return 0;
}
```

```click
resource packed(node: struct node*) {
    owns node->word;
    let next: struct node* = node;
}

verifying "resource_witness_requires_where.c";

int32 unused(struct node* node) {
    ensures result == 0 by auto;
}
```

```expect
fail: a resource body `let` must be `let name: type where proposition;`
```
