# A model-field pointer to another struct fails the loop join

The packed word's origin is a model field declared `struct other_node*`. The
decoded pointer designates a `struct other_node`, not the `struct model_node`
that `p` designates at the loop head. The back edge would change `p`'s object
class, so the loop join refuses it. The join does not take the head's class,
and the cast's destination type supplies no class. Compare
`packed_model_pointer_loop_object_class.md`, where the field declares the
same struct and the proof verifies.

```c filename=packed_other.c
struct model_node { uint64 parent_word; };
struct other_node { uint64 parent_word; };
void follow_model(struct model_node* p, int32 more) {
    while (more) { p = (struct model_node*)p->parent_word; more = more - 1; }
}
```
```click
verifying "packed_other.c";
spec enum PackedLink { At(struct other_node*), }
resource model_link(p: struct model_node*) {
    field word: uint64;
    field model: PackedLink;
    match model { PackedLink::At(q) => { owns p->parent_word; fact p->parent_word == word; fact q == p; fact word == address(q); fact (p->parent_word as (struct model_node *)) == q; }, }
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
fail: loop-head object class
```
