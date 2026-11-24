# A fold requires an explicit same-named child

The proof owns a folded `left` of the required family. The fold must still
supply `left: left` in its input map.

```c filename=a_fold_requires_an_explicit_same_named_child.c
void join(int32* p, int32* lp, int32* rp, int32* q, int32 value) { *p = value; }
```

```click
verifying "a_fold_requires_an_explicit_same_named_child.c";

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

void join(int32* p, int32* lp, int32* rp, int32* q, int32 value) {
    consumes p[0..1];
    consumes left: tree(lp);
    consumes right: tree(rp);
    produces root: tree(p);
} by {
    step_until(function.exit);
    let root = fold(tree(p), { model: Tree::Branch(value, lp, left.model, rp, right.model), right: right });
    close();
}
```

```expect
fail: fold of `tree` must supply its named child `left` in its input map: `{ left: name }`
```
