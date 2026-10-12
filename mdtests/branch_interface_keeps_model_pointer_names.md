# A branch interface retains its model-bound pointer spelling

The interface exports a packed word using the outer model binding `id`.
A later snapshot rewrite cancels the extra word. The loaded child has its own
typed-place guarantee; address equality with `q` supplies no such validity.
Expansion must retain the model name rather than print an internal pointer.

```c filename=probe.c
struct Node { unsigned long tag; struct Node *next; int32 other; };
void set_word(struct Node *q, struct Node *r, unsigned long stamp) {
    q->tag = (unsigned long)r + stamp;
}
void put(struct Node *p, struct Node *q, int32 x, unsigned long stamp) {
    struct Node *child = p->next;
    struct Node *r = q->next;
    set_word(child, r, stamp);
    if (x <= 0) { q->other = 0; } else { q->other = 1; }
}
```

```click
verifying "probe.c";
spec enum Model { At(struct Node*) }
resource identity(p: struct Node*) {
    field model: Model;
    match model { Model::At(id) => { owns p->other; fact p == id; }, }
}
void set_word(struct Node* q, struct Node* r, uint64 stamp) {
    owns q->tag;
    ensures q->tag == address(r) + stamp;
} by { execute(); simp(); }
void put(struct Node *p, struct Node *q, int32 x, uint64 stamp) {
    owns p->next;
    requires p->next == q;
    owns p->next->tag;
    owns q->other;
    owns q->next;
    consumes s: identity(q->next);
    ensures 1 == 1;
} by {
    match s.model { Model::At(id) => {
        unfold(s);
        step(); step(); step(); step();
        step(set_word(child, r, stamp), {});
        have child == q;
        have child->tag == address(id) + stamp by { rewrite(id == r); simp(); }
        branch ensuring { fact child->tag == address(id) + stamp; } then {
            step();
            have child->tag == address(id) + stamp;
        } else {
            step();
            have child->tag == address(id) + stamp;
        }
        mark joined;
        have at(joined, child->tag) - stamp == address(id);
        execute(); simp();
    }, }
}
```

```expect
pass
```
