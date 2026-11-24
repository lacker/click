# An address-only C return cannot provide a typed model pointer

```c filename=returned.c
struct model_node { uint64 word; };
struct model_node* cast_address(void* p) { return (struct model_node*)p; }
void wrapped(struct model_node* p) {}
void caller(void* p) {
    struct model_node* q = cast_address(p);
    wrapped(q);
}
```

```click
verifying "returned.c";
spec enum NodeRef { At(struct model_node*), }
resource token() { field model: NodeRef; }
struct model_node* cast_address(void* p) {
    ensures address(result) == address(p);
} by { step_until(function.exit); close(); }
void wrapped(struct model_node* p) { produces held: token(); ensures held.model == NodeRef::At(p); } by {
    step_until(function.exit); let held = fold(token(), { model: NodeRef::At(p) });
}
void caller(void* p) { produces held: token(); ensures true; } by {
    step(); step(); step(); let { held: held } = step(wrapped);
}
```

```expect
fail: requires original object class `struct model_node` or null
```
