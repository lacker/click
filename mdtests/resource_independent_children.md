# Independent recursive children

This synthetic resource owns payload cells; it is not yet a concrete C tree
with stored child-pointer fields. It exercises one-layer child ownership.

```c filename=resource_independent_children.c
int32 read_left(int32* p, int32* left, int32* right) { return *left; }
void init(int32* p, int32* left, int32* right, int32 value) { *p = value; }
```

```click
verifying "resource_independent_children.c";

spec enum Tree { Leaf(int32), Branch(int32, int32*, Tree, int32*, Tree) }
resource tree(p: int32*) {
    field model: Tree;
    match model {
        Tree::Leaf(value) => { owns p[0..1]; fact p[0] == value; },
        Tree::Branch(value, lp, lm, rp, rm) => {
            owns p[0..1];
            owns left: tree(lp);
            owns right: tree(rp);
            fact p[0] == value;
            fact left.model == lm;
            fact right.model == rm;
        },
    }
}

int32 read_left(int32* p, int32* left, int32* right) {
    owns root: tree(p);
    requires root.model == Tree::Branch(1, left, Tree::Leaf(2), right, Tree::Leaf(3));
    ensures result == 2;
    ensures root.model == old(root.model);
} by {
    unfold(root) as { left: l, right: r };
    unfold(l);
    execute();
    let l = fold(tree(left), { model: Tree::Leaf(2) });
    let root = fold(tree(p), { model: old(root.model) }, { left: l, right: r });
    simp();
}

void init(int32* p, int32* left, int32* right, int32 value) {
    consumes p[0..1];
    consumes l: tree(left);
    consumes r: tree(right);
    produces root: tree(p);
    ensures root.model == Tree::Branch(value, left, old(l.model), right, old(r.model));
} by {
    execute();
    let root = fold(tree(p), { model: Tree::Branch(value, left, l.model, right, r.model) }, { left: l, right: r });
    simp();
}
```

```expect
pass
```
