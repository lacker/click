# Guarded resource facts survive a disjoint store

```c filename=guarded.c
struct base { struct base* left; struct base* right; uint64 padding; };
struct cell { struct base base; int32 value; };
void consume_child(struct base *p);
int32 f(struct cell* root) {
    struct base* child = root->base.left;
    int32 value = ((struct cell*)(void*)child)->value;
    root->value = value;
    consume_child(child);
    return ((struct cell*)(void*)child)->value;
}
```

```click
verifying "guarded.c";
resource child_value(p: struct base*) {
    field number: int32;
    if p != 0 {
        owns ((struct cell*)(void*)p)->value;
        fact ((struct cell*)(void*)p)->value == number;
    }
}
extern void consume_child(struct base *p) {
    consumes state: child_value(p);
}
int32 f(struct cell* root) {
    requires root != 0;
    views root->base.left;
    consumes child: child_value(root->base.left);
    owns root->value;
    requires root->base.left != 0;
    requires root->base.left != (struct base*)(void*)root;
    ensures result == old(child.number);
    ensures root->value == old(child.number);
} by { unfold(child); step(); step(); step(); step(); step(); fold(child); step(); step(); simp(); }
```

```expect
fail: missing resource fact
```
