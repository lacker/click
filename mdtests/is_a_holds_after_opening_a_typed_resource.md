# A resource body's typed call makes its pointer `is_a` that type

`token(p)` promises `valid(p) == 1`, and `valid` takes a `struct node*`.
Opening the held token recovers that typed call's domain, so the proof may
state that `p` points to a `struct node` as `is_a<struct node>(p)`.

```c filename=is_a_holds_after_opening_a_typed_resource.c
struct node { uint64 word; };
void keep(struct node* p) {}
```

```click
verifying "is_a_holds_after_opening_a_typed_resource.c";
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
    unfold(held);
    step();
    have is_a<struct node>(p) by close();
    let held = fold(token(p), { model: old(held.model) });
}
```

```expect
pass
```
