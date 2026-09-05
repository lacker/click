# A tagged word loaded from a field converts back

The word lives in a struct field, and a precondition relates that field to
`next`'s address plus a tag. The load, mask, and cast recover `next`, so the
recovered pointer can be dereferenced under the caller's view of it.

```c filename=tagged_pointer_from_field_fact.c
struct node {
    int32 value;
    unsigned long word;
};

int32 parent_value(struct node* node, struct node* next) {
    struct node* parent = (struct node*)(node->word & ~3);
    return parent->value;
}
```

```click
verifying "tagged_pointer_from_field_fact.c";

int32 parent_value(struct node* node, struct node* next) {
    requires node != 0;
    requires next != 0;
    requires aligned(next, 8);
    requires node->word == address(next) + 1;
    views node->word;
    views next->value;
    ensures result == next->value;
} by {
    execute();
    simp();
}
```

```expect
pass
```
