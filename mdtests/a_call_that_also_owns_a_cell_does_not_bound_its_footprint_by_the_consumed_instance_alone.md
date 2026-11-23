# A call that also owns a cell does not bound its footprint by the consumed instance alone

When the callee also owns `*slot`, the call's footprint bound is the consumed instance together with that cell. The consumed instance alone does not contain the footprint, so the cell is not carried across the call.

```c filename=consuming.c
struct node { struct node *next; };
void touch(struct node *child, int *slot) {}
void caller(struct node *child, int *slot) { touch(child, slot); }
```

```click
import click::separation;
verifying "consuming.c";
resource box(p: struct node*) {
    field tag: int32;
    owns p->next;
}
void touch(struct node* child, int32* slot) {
    consumes b: box(child);
    owns *slot;
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
    have separate(b, memory(*slot)) by { known(); }
    mark before_call;
    let { c: c } = step(touch, { b: b });
    have contains(at(before_call, b), statement(0).footprint) by { known(); }
}
```

```expect
fail: `known()` could not close the current goal
```
