# An owned resource with an unconditional body is not separate from its own cell

The contract entry states a resource with an unconditional body both as an
owned member and as the members its body expands to. Those are two
descriptions of the same bytes, never two owners, so the resource is not
separate from the cell its own body owns.

```c filename=owned.c
struct node { struct node *next; };
void caller(struct node *child, int *slot) { }
```

```click
verifying "owned.c";
resource plain(p: struct node*) { owns p->next; }
void caller(struct node* child, int32* slot) {
    owns plain(child);
    owns *slot;
} by {
    have separate(plain(child), memory(child->next)) by { known(); }
}
```

```expect
fail: `known()` could not close the current goal
```
