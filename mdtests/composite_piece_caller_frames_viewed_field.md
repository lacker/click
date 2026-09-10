# A caller owning the whole composite frames the field the callee only views

The callee views `cell(n)` and owns `n->value`. The caller owns the folded
composite. The call unfolds it, hands the callee the owned field with a view of
the rest, and gets everything back; `n->next` was never in the callee's write
footprint, so the caller keeps its pre-call value with no effect clause and no
`frame`. Folding the composite back restores the caller's own contract.

```c filename=composite_piece_caller_frames_viewed_field.c
struct node {
    int32 value;
    struct node* next;
};

void set_value(struct node* n, int32 v) {
    n->value = v;
}

void caller(struct node* n) {
    set_value(n, 7);
}
```

```click
resource cell(n: struct node*) {
    owns n->value;
    owns n->next;
}

verifying "composite_piece_caller_frames_viewed_field.c";

void set_value(struct node* n, int32 v) {
    views cell(n);
    owns n->value;
    ensures n->value == v;
} by {
    step();
    step();
    simp();
}

void caller(struct node* n) {
    owns cell(n);
    ensures n->next == old(n->next);
} by {
    step();
    fold(cell(n));
    step();
    simp();
}
```

```expect
pass
```
