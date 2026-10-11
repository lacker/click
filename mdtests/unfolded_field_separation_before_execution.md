# An unfolded field is separate from a field of another owned object

The parent is owned as a whole three-field struct. The separation must be
available immediately after unfolding the child, before any C step refreshes
the published ownership composition.

```c filename=update.c
struct node { uint64 word; struct node *left; struct node *right; };
void update(struct node* parent, struct node* child) {
    if (child) child->word = 1;
}
```

```click
resource cell(p: struct node*) {
    field value: uint64;
    owns p->word;
    fact p->word == value;
    fact p != 0;
}
verifying "update.c";
void update(struct node* parent, struct node* child) {
    owns *parent;
    owns c: cell(child);
} by {
    unfold(c);
    have separate(memory(parent->word), memory(child->word)) by assumption();
    step();
    step();
    let c = fold(cell(child), { value: 1u64 });
    execute();
    simp();
}
```

```expect
pass
```
