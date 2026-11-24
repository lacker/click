# A resource instance is not named at a mark where it is not held

`at(mark, name)` names the instance held at that mark. After a call consumes
it, a later mark does not hold it, and the spelling is refused.

```c filename=named.c
struct node { struct node *next; };
void touch(struct node *child) {}
void caller(struct node *child, int *slot) { touch(child); }
```

```click
verifying "named.c";
resource box(p: struct node*) {
    field tag: int32;
    owns p->next;
}
void touch(struct node* child) {
    consumes b: box(child);
    produces c: box(child);
} by {
    unfold(b);
    let c = fold(box(child), { tag: 0 });
}
void caller(struct node* child, int32* slot) {
    consumes b: box(child);
    owns *slot;
    produces c: box(child);
} by {
    let { c: c } = step(touch, { b: b });
    mark later;
    have separate(at(later, b), memory(*slot)) by { close(); }
}
```

```expect
fail: resource instance `b` is not owned at this state
```
