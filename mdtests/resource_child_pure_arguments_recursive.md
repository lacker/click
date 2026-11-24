# Recursive child addresses from model getters

```c filename=resource_child_pure_arguments_recursive.c
int32 read_left(int32* p, int32* left, int32* right) { return *left; }
```
```click
verifying "resource_child_pure_arguments_recursive.c";
spec enum Tree { Leaf(int32*, int32), Branch(int32*, Tree, Tree) }
function root_pointer(model: Tree) -> int32* {
    match model {
        Tree::Leaf(p, value) => p,
        Tree::Branch(p, left, right) => p,
    }
}
resource cache(p: int32*) {
    field model: Tree;
    match model {
        Tree::Leaf(identity, value) => { owns p[0..1]; fact p == identity; fact p[0] == value; },
        Tree::Branch(identity, left_model, right_model) => {
            owns p[0..1];
            owns left: cache(root_pointer(left_model));
            owns right: cache(root_pointer(right_model));
            fact p == identity;
            fact left.model == left_model;
            fact right.model == right_model;
        },
    }
}
int32 read_left(int32* p, int32* left, int32* right) {
    owns root: cache(p);
    requires root.model == Tree::Branch(p, Tree::Leaf(left, 2), Tree::Leaf(right, 3));
    ensures result == 2;
    ensures root.model == old(root.model);
} by {
    have root_pointer(Tree::Leaf(left, 2)) == left by { unfold(root_pointer(Tree::Leaf(left, 2))); close(); }
    have root_pointer(Tree::Leaf(right, 3)) == right by { unfold(root_pointer(Tree::Leaf(right, 3))); close(); }
    let { left: l, right: r } = unfold(root);
    unfold(l);
    step_until(function.exit);
    let l = fold(cache(left), { model: Tree::Leaf(left, 2) });
    let root = fold(cache(p), { model: Tree::Branch(p, Tree::Leaf(left, 2), Tree::Leaf(right, 3)), left: l, right: r });
    close();
}
```
```expect
pass
```
