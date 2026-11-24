# An undersized allocation cannot establish a complete struct object

```c filename=heap.c
struct node { uint64 word; };
int32 accept(struct node* p) { return 7; }
int32 allocated() {
    struct node* p = malloc(1);
    if (!p) return 7;
    int32 result = accept(p);
    free(p);
    return result;
}
```

```click
verifying "heap.c";
spec enum NodeRef { At(struct node*), }
resource token() { field model: NodeRef; }
int32 accept(struct node* p) { produces held: token(); ensures result == 7; ensures held.model == NodeRef::At(p); } by {
    step_until(function.exit); let held = fold(token(), { model: NodeRef::At(p) }); close();
}
int32 allocated() { ensures result == 7; }
```

```expect
fail: requires original object class `struct node` or null
```
