# Callback preservation through a composite-owned write

```c filename=callback.c
struct node { int value; };
struct callbacks { void (*invoke)(void); };
void update(struct node *p, const struct callbacks *cb) {
    p->value = 1;
    cb->invoke();
}
```
```click
verifying "callback.c";
contract void Callback() { ensures 1 == 1; }
resource node_cell(p: struct node*) { owns p->value; }
resource callback_table(cb: const struct callbacks*) {
    views cb->invoke;
    fact Callback(cb->invoke);
}
resource node_layer_1(p: struct node*) { owns node_cell(p); }
resource callback_layer_1(cb: const struct callbacks*) { owns callback_table(cb); }
resource node_layer_2(p: struct node*) { owns node_layer_1(p); }
resource callback_layer_2(cb: const struct callbacks*) { owns callback_layer_1(cb); }
void update(struct node* p, const struct callbacks* cb) {
    owns node_layer_2(p);
    views callback_layer_2(cb);
    ensures p->value == 1;
} by {
    unfold(node_layer_2(p));
    observe(callback_layer_2(cb));
    unfold(node_layer_1(p));
    observe(callback_layer_1(cb));
    unfold(node_cell(p));
    open(callback_table(cb)) {
        have separate(memory(cb->invoke), memory(p->value));
        step_until(function.exit);
    }
    fold(node_cell(p));
    fold(node_layer_1(p));
    fold(node_layer_2(p));
    solve();
}
```
```expect
pass
```
