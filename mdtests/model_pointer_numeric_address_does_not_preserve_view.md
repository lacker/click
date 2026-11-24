# A numeric packed address does not preserve the full pointer value

Matching the model recovers object-type evidence, but numeric address
equality does not recover the saved pointer's provenance and bounds.
The full-pointer relation in the positive control is deliberately absent.

```c filename=packed_model.c
struct model_node { uint64 parent_word; };
void follow_model(struct model_node* p, int32 more) {
    while (more) { p = (struct model_node*)p->parent_word; more = more - 1; }
}
```
```click
verifying "packed_model.c";
spec enum PackedLink { At(struct model_node*), }
resource model_link(p: struct model_node*) {
    field word: uint64;
    field model: PackedLink;
    match model { PackedLink::At(q) => { owns p->parent_word; fact p->parent_word == word; fact q == p; fact word == address(q); }, }
}
void follow_model(struct model_node* p, int32 more) {
    owns held: model_link(p);
    requires 0 <= more;
    ensures 1 == 1;
} by {
    loop {
        owns held: model_link(old(p));
        decreases more;
        invariant p == old(p);
        invariant 0 <= more;
        initialize by close();
        maintain by {
            match held.model { PackedLink::At(q) => {
            let { word: saved_word } = unfold(held);
            have p->parent_word == address(q) by { rewrite(p, old(p)); close(); }
            step(); step();
            let held = fold(model_link(old(p)), { word: saved_word, model: PackedLink::At(q) });
            } }
        }
    }
}
```
```expect
fail: closure body did not prove every invariant obligation
```
