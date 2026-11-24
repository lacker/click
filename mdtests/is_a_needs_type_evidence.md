# `is_a` is refused before the proof has type evidence

Before the held token is opened, the parameter `p` has only its C access
typing, which says nothing about the object it points to. `is_a<struct
node>(p)` is not yet known.

```c filename=is_a_needs_type_evidence.c
struct node { uint64 word; };
void keep(struct node* p) {}
```

```click
verifying "is_a_needs_type_evidence.c";
spec enum Ref { At(struct node*), }
function valid(p: struct node*) -> int32 { 1 }
resource token(p: struct node*) {
    field model: int;
    fact valid(p) == 1;
}
void keep(struct node* p) {
    owns held: token(p);
    ensures held.model == old(held.model);
} by {
    have is_a<struct node>(p) by close();
    unfold(held);
    step();
    have Ref::At(p) == Ref::At(p) by { close(); }
    let held = fold(token(p), { model: old(held.model) });
}
```

```expect
fail: `have` failed for `is_a<struct node>(p)`
```
