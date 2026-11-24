# An owned resource instance with fields is not separate from its own cell

An owned resource instance is separate from the other resources held beside
it, never from a cell its own body owns.

```c filename=owned.c
struct node { struct node *next; };
void caller(struct node *child, int *slot) { }
```

```click
verifying "owned.c";
resource box(p: struct node*) {
    field tag: int32;
    owns p->next;
}
void caller(struct node* child, int32* slot) {
    owns b: box(child);
    owns *slot;
} by {
    have separate(b, memory(child->next)) by { close(); }
}
```

```expect
fail: could not establish `separate(b, memory(child->next))`
```
