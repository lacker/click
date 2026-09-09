# Recursive named child resources

Only the selected constructor's immediate child is exposed. The parent's
open handle keeps its name, and the child must be folded before the parent.

```c filename=resource_recursive_children.c
int32 read_root(int32* p, int32* next) { return *p; }
int32 read_left(int32* p, int32* left, int32* right) { return *left; }
```

```click
verifying "resource_recursive_children.c";

spec enum Chain { End, More(int32*, Chain) }

resource chain(p: int32*) {
    field model: Chain;
    match model {
        Chain::End => { fact p == 0; },
        Chain::More(next, rest) => {
            owns p[0..1];
            owns tail: chain(next);
            fact tail.model == rest;
        },
    }
}

int32 read_root(int32* p, int32* next) {
    owns root: chain(p);
    requires root.model == Chain::More(next, Chain::End);
    ensures root.model == old(root.model);
} by {
    unfold(root);
    unfold(root.tail);
    execute();
    fold(root.tail);
    fold(root);
    simp();
}

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
    unfold(root);
    unfold(root.left);
    execute();
    fold(root.left);
    fold(root);
    simp();
}
```

```expect
pass
```
