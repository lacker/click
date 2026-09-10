# A store into a viewed field beside the owned piece is rejected

The function views `cell(n)` and owns only `n->value`. The store into
`n->next` targets memory the function merely views, so it fails at the store
for want of an owned resource rather than being framed away.

```c filename=composite_piece_rejects_store_outside_owned_field.c
struct node {
    int32 value;
    struct node* next;
};

void set_next_to_self(struct node* n) {
    n->next = n;
}
```

```click
resource cell(n: struct node*) {
    owns n->value;
    owns n->next;
}

verifying "composite_piece_rejects_store_outside_owned_field.c";

void set_next_to_self(struct node* n) {
    views cell(n);
    owns n->value;
} by {
    step();
    step();
    simp();
}
```

```expect
fail: missing resource fact
```
