# `let` introduces the instance a called function produces

`init` consumes two child trees and produces a parent. `build` binds the two
`consumes` binders through the call map and introduces the produced instance
with `let`. `build_parent` does the same and then folds the produced instance
in as the left child of a larger tree, so the produced name is an ordinary
owned instance afterwards.

```c filename=c_call_binder_transport_produces.c
void init(int32* p, int32* left, int32* right, int32 value) { *p = value; }
void build(int32* p, int32* left, int32* right, int32 value) {
    init(p, left, right, value);
}
void build_parent(int32* q, int32* p, int32* left, int32* right, int32* other,
                  int32 value) {
    init(p, left, right, value);
    *q = value;
}
```

```click
verifying "c_call_binder_transport_produces.c";

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

void build(int32* p, int32* left, int32* right, int32 value) {
    consumes p[0..1];
    consumes a: tree(left);
    consumes b: tree(right);
    produces node: tree(p);
    ensures node.model == Tree::Branch(value, left, old(a.model), right, old(b.model));
} by {
    let node = step(init(p, left, right, value), { l: a, r: b });
    execute();
    simp();
}

void build_parent(int32* q, int32* p, int32* left, int32* right, int32* other,
                  int32 value) {
    consumes q[0..1];
    consumes p[0..1];
    consumes a: tree(left);
    consumes b: tree(right);
    consumes far: tree(other);
    produces top: tree(q);
    ensures top.model == Tree::Branch(value, p,
        Tree::Branch(value, left, old(a.model), right, old(b.model)), other, old(far.model));
} by {
    let node = step(init(p, left, right, value), { l: a, r: b });
    execute();
    let top = fold(tree(q), { model: Tree::Branch(value, p,
        Tree::Branch(value, left, old(a.model), right, old(b.model)), other, old(far.model)) },
        { left: node, right: far });
    simp();
}
```

```expect
pass
```
