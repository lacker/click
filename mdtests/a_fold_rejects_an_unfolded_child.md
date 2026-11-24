# A fold rejects an unfolded child

An explicit child binding has to name an instance still owned in folded form.

```c filename=a_fold_rejects_an_unfolded_child.c
int32 read_left(int32* p, int32* lp, int32* rp) { return *lp; }
```

```click
verifying "a_fold_rejects_an_unfolded_child.c";

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

int32 read_left(int32* p, int32* lp, int32* rp) {
    owns root: tree(p);
    requires root.model == Tree::Branch(1, lp, Tree::Leaf(2), rp, Tree::Leaf(3));
    ensures result == 2;
    ensures root.model == old(root.model);
} by {
    let { left: left, right: right } = unfold(root);
    unfold(left);
    step_until(function.exit);
    let root = fold(tree(p), { model: old(root.model), left: left, right: right });
    close();
}
```

```expect
fail: child `left` is not owned in folded form
```
