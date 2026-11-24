# `is_a` with another type is not the recovered evidence

Opening the token recovers that `p` points to a `struct node`. That is not
evidence that it points to a `struct node*`, so `is_a<struct node*>(p)`
stays unknown.

```c filename=is_a_names_the_type_of_the_evidence.c
struct node { uint64 word; };
void keep(struct node* p) {}
```

```click
verifying "is_a_names_the_type_of_the_evidence.c";
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
    have is_a<struct node*>(p) by close();
    let held = fold(token(p), { model: old(held.model) });
}
```

```expect
fail: `have` failed for `is_a<struct node*>(p)`
```
