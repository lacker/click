# A resource witness must be a pointer

```c filename=resource_witness_pointer_type.c
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
    let mark: int32 where mark == 0;
}

verifying "resource_witness_pointer_type.c";

int32 unused(struct node* node) {
    ensures result == 0 by auto;
}
```

```expect
fail: resource witness `mark` must have a pointer type
```
