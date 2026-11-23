# A resource address alias does not invent a non-self link

This resource does not require a non-self child. Matching its address
identity must not establish that missing fact.

```c filename=pointer_nonself.c
struct item { uint64 word; struct item* child; };
void keep(struct item* root) {}
```
```click
verifying "pointer_nonself.c";
spec enum Tree { Leaf(struct item*), Parent(struct item*, Tree) }
resource chain(p: struct item*) {
    field model: Tree;
    match model {
        Tree::Leaf(identity) => { owns p->word; fact p == identity; },
        Tree::Parent(identity, rest) => {
            owns p->child;
            owns child: chain(p->child);
            fact p == identity;
            fact child.model == rest;
        },
    }
}
void keep(struct item* root) {
    consumes state: chain(root);
    ensures 1 == 1;
} by {
    match state.model {
        Tree::Leaf(identity) => { unfold(state); step_until(function.exit); solve(); },
        Tree::Parent(identity, rest) => {
            let { child: inner } = unfold(state);
            match inner.model {
                Tree::Leaf(parent) => { unfold(inner); step_until(function.exit); solve(); },
                Tree::Parent(parent, tail) => {
                    let { child: leaf } = unfold(inner);
                    have parent->child != parent by { known(); }
                    step_until(function.exit); solve();
                },
            }
        },
    }
}
```
```expect
fail: `known()` could not close the current goal
```
