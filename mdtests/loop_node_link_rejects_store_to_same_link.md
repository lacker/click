# A node's link does not frame across a store to that same link in a loop

The `__rb_erase_color` case 3 shape, except that the last store writes the
sibling's own `right` link through the `sibling` local, another spelling of
`sid`. The sibling's link read after the stores is not its value before them,
and the frontier's load-equality bridge must not publish the comparison.

```c filename=rotate.c
#define WRITE_ONCE(x, value) ({ typeof(x) __value = (value); (*(volatile typeof(x) *)&(x)) = __value; __value; })
struct node { unsigned long tag; struct node *right; struct node *left; };
void rotate(struct node *parent) {
    struct node *sibling, *tmp1, *tmp2;
    while (1) {
        sibling = parent->right;
        tmp2 = sibling->left;
        tmp1 = tmp2->right;
        WRITE_ONCE(sibling->left, tmp1);
        WRITE_ONCE(tmp2->right, sibling);
        WRITE_ONCE(sibling->right, tmp2);
        break;
    }
}
```

```click
verifying "rotate.c";
spec enum Tree { Empty, Node(struct node*, Tree, Tree) }
resource tree(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(id, lm, rm) => {
            owns p->tag;
            owns p->right;
            owns p->left;
            owns left: tree(p->left);
            owns right: tree(p->right);
            fact p != 0;
            fact p == id;
            fact left.model == lm;
            fact right.model == rm;
        },
    }
}
void rotate(struct node* parent) {
    consumes t: tree(parent);
    requires t.model != Tree::Empty;
    requires parent->right != 0;
    requires parent->right->left != 0;
} by {
    step_until(loop(0).entry);
    loop {
        owns t: tree(parent);
        invariant t.model != Tree::Empty;
        invariant parent->right != 0;
        invariant parent->right->left != 0;
        decreases 0;
        initialize by solve();
        maintain by {
            match t.model {
                Tree::Empty => { contradiction(t.model == Tree::Empty); },
                Tree::Node(id, lm, rm) => {
                    let { left: l, right: s } = unfold(t);
                    match s.model {
                        Tree::Empty => {
                            unfold(s);
                            contradiction(parent->right == 0);
                        },
                        Tree::Node(sid, slm, srm) => {
                            let { left: sl, right: sr } = unfold(s);
                            match sl.model {
                                Tree::Empty => {
                                    unfold(sl);
                                    contradiction(parent->right->left == 0);
                                },
                                Tree::Node(iid, ilm, irm) => {
                                    let { left: il, right: ir } = unfold(sl);
                                    step(); step(); step(); // Read the three links.
                                    have sibling == sid;
                                    have tmp2 == iid;
                                    mark inner_inputs;
                                    step(); step(); step(); // The three link stores.
                                    have sid->right == at(inner_inputs, sid->right) by known();
                                },
                            }
                        },
                    }
                },
            }
        }
    }
}
```

```expect
fail: `known()` could not close the current goal
```
