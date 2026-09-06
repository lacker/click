# a resource owning a uint64 field unfolds to a cell of that type

A composite body that owns one `unsigned long` field must expose that field
as a 64-bit cell when unfolded, matching the kernel's expansion of the same
definition, so the proof can read the word and fold the body back.

```c filename=resource_uint64_field_unfold.c
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};

unsigned long word_of(struct rb_node *node) {
    return node->__rb_parent_color;
}
```

```click
resource linked(node: struct rb_node*) {
    owns node->__rb_parent_color;
    fact aligned(node, 8);
}

verifying "resource_uint64_field_unfold.c";

unsigned long word_of(struct rb_node* node) {
    requires node != 0;
    owns linked(node);
    ensures result == node->__rb_parent_color;
} by {
    unfold(linked(node));
    execute();
    fold(linked(node));
    simp();
}
```

```expect
pass
```
