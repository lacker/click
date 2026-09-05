# A successful heap allocation is allocator-aligned

Under the LP64 profile the C library allocator returns storage aligned for
every fundamental type, so a fresh allocation's base is 16-byte aligned and
its constant field displacements inherit that. No contract clause states the
alignment; it follows from the allocation itself.

```c filename=aligned_from_malloc.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* aligned_from_malloc() {
    struct node* node = malloc(sizeof(struct node));
    if (node == 0) {
        return 0;
    }
    node->value = 0;
    node->word = 0;
    return node;
}
```

```click
resource owned_node(node: struct node*) {
    if node != 0 {
        contains allocation(node, sizeof(struct node));
        owns object(node);
    }
}

verifying "aligned_from_malloc.c";

struct node* aligned_from_malloc() {
    produces owned_node(result);
    ensures result != 0 implies aligned(result, 8);
    ensures result != 0 implies aligned(&result->word, 8);
} by {
    execute();
    fold(owned_node(result));
    simp();
}
```

```expect
pass
```
