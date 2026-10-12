# Separation goals use the same checked borrow partition

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
void update(struct node* p, const struct callbacks* cb) {
    owns node_cell(p);
    views callback_table(cb);
    ensures p->value == 1;
} by {
    unfold(node_cell(p));
    open(callback_table(cb)) {
        have separate(memory(p->value), memory(cb->invoke));
        execute();
    }
    fold(node_cell(p));
    simp();
}
```
```expect
pass
```
