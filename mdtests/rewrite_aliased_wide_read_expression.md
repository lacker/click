# Rewrite transports a 64-bit read inside a mask through a checked alias

The cited mask equality is already known through the shared equality graph.
Rewriting it into the goal must preserve its read kind and state while
matching the pointer obtained from nested resources with the parameter alias.

```c filename=nested_model_read_alias.c
struct item { uint64 word; struct item* child; };
uint64 lowbit(struct item* root, struct item* parent, struct item* node) { return node->word & 1; }
```
```click
verifying "nested_model_read_alias.c";
spec enum Color { Red, Black }
function color_bit(color: Color) -> int32 {
    match color { Color::Red => 0, Color::Black => 1, }
}
spec enum Tree { Leaf(struct item*), Parent(struct item*, Tree) }
resource chain(p: struct item*) {
    field model: Tree;
    match model {
        Tree::Leaf(identity) => {
            owns p->word;
            fact p == identity;
            fact (p->word & 1) == color_bit(Color::Red);
        },
        Tree::Parent(identity, child_model) => {
            owns p->child;
            owns child: chain(p->child);
            fact p == identity;
            fact child.model == child_model;
        },
    }
}
uint64 lowbit(struct item* root, struct item* parent, struct item* node) {
    consumes state: chain(root);
    requires state.model == Tree::Parent(root, Tree::Parent(parent, Tree::Leaf(node)));
    ensures result == 0;
} by {
    let { child: child } = unfold(state);
    let { child: leaf } = unfold(child);
    unfold(leaf);
    unfold(color_bit(Color::Red));
    have (node->word & 1) == color_bit(Color::Red) by { known(); }
    have color_bit(Color::Red) == 0 by { known(); }
    have (node->word & 1) == 0 by {
        rewrite((node->word & 1), color_bit(Color::Red));
        rewrite(color_bit(Color::Red), 0);
        normalize();
    }
}
```
```expect
pass
```
