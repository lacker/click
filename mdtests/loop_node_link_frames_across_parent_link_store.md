# A node's link frames across a store to its parent's link in a loop

The loop rotates a parent's right subtree (the `__rb_erase_color` case 3
shape). After `parent->right` is overwritten, the sibling's own `right` link
is compared with its value before the stores. The two reads are pointer loads
of one cell at two states, so the goal is a same-block pointer equality.
An explicit separation fact and explicit preservation proof preserve the inner
node's freshly stored right link across the parent's store. Recovering that
value must not require finding its older store in memory history.

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
        WRITE_ONCE(parent->right, tmp2);
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
        initialize by close();
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
                                    mark before_link_0;
                                    have separate(memory(sibling->left), memory(sid->right)) by close();
                                    have separate(memory(sibling->left), memory(iid->left)) by close();
                                    have separate(memory(sibling->left), memory(parent->left)) by close();
                                    step();
                                    have separate(loop(0).statement(3).footprint, memory(sid->right)) by {
                                        close() using { separate(memory(sibling->left), memory(sid->right)); };
                                    }
                                    have sid->right == at(before_link_0, sid->right) by {
                                        preserve(memory(sid->right), loop(0).statement(3));
                                    }
                                    have separate(loop(0).statement(3).footprint, memory(iid->left)) by {
                                        close() using { separate(memory(sibling->left), memory(iid->left)); };
                                    }
                                    have iid->left == at(before_link_0, iid->left) by {
                                        preserve(memory(iid->left), loop(0).statement(3));
                                    }
                                    have separate(loop(0).statement(3).footprint, memory(parent->left)) by {
                                        close() using { separate(memory(sibling->left), memory(parent->left)); };
                                    }
                                    have parent->left == at(before_link_0, parent->left) by {
                                        preserve(memory(parent->left), loop(0).statement(3));
                                    }
                                    have sid->left == tmp1;
                                    mark before_link_1;
                                    have separate(memory(tmp2->right), memory(sid->right)) by close();
                                    have separate(memory(tmp2->right), memory(iid->left)) by close();
                                    have separate(memory(tmp2->right), memory(parent->left)) by close();
                                    have separate(memory(tmp2->right), memory(sid->left)) by close();
                                    step();
                                    have separate(loop(0).statement(4).footprint, memory(sid->right)) by {
                                        close() using { separate(memory(tmp2->right), memory(sid->right)); };
                                    }
                                    have sid->right == at(before_link_1, sid->right) by {
                                        preserve(memory(sid->right), loop(0).statement(4));
                                    }
                                    have sid->right == at(inner_inputs, sid->right) by {
                                        rewrite(sid->right, at(before_link_1, sid->right));
                                        close();
                                    }
                                    have separate(loop(0).statement(4).footprint, memory(iid->left)) by {
                                        close() using { separate(memory(tmp2->right), memory(iid->left)); };
                                    }
                                    have iid->left == at(before_link_1, iid->left) by {
                                        preserve(memory(iid->left), loop(0).statement(4));
                                    }
                                    have iid->left == at(inner_inputs, iid->left) by {
                                        rewrite(iid->left, at(before_link_1, iid->left));
                                        close();
                                    }
                                    have separate(loop(0).statement(4).footprint, memory(parent->left)) by {
                                        close() using { separate(memory(tmp2->right), memory(parent->left)); };
                                    }
                                    have parent->left == at(before_link_1, parent->left) by {
                                        preserve(memory(parent->left), loop(0).statement(4));
                                    }
                                    have parent->left == at(inner_inputs, parent->left) by {
                                        rewrite(parent->left, at(before_link_1, parent->left));
                                        close();
                                    }
                                    have separate(loop(0).statement(4).footprint, memory(sid->left)) by {
                                        close() using { separate(memory(tmp2->right), memory(sid->left)); };
                                    }
                                    have sid->left == at(before_link_1, sid->left) by {
                                        preserve(memory(sid->left), loop(0).statement(4));
                                    }
                                    have iid->right == sid;
                                    have defined(iid->right) by { rewrite(iid, tmp2); close(); }
                                    mark before_parent_store;
                                    have separate(memory(parent->right), memory(sid->right)) by close();
                                    have separate(memory(parent->right), memory(iid->left)) by close();
                                    have separate(memory(parent->right), memory(parent->left)) by close();
                                    have separate(memory(parent->right), memory(sid->left)) by close();
                                    have separate(memory(parent->right), memory(iid->right)) by close();
                                    step();
                                    have separate(loop(0).statement(5).footprint, memory(sid->right)) by {
                                        close() using { separate(memory(parent->right), memory(sid->right)); };
                                    }
                                    have sid->right == at(before_parent_store, sid->right) by {
                                        preserve(memory(sid->right), loop(0).statement(5));
                                    }
                                    have sid->right == at(inner_inputs, sid->right) by {
                                        rewrite(sid->right, at(before_parent_store, sid->right));
                                        close();
                                    }
                                    have separate(loop(0).statement(5).footprint, memory(iid->left)) by {
                                        close() using { separate(memory(parent->right), memory(iid->left)); };
                                    }
                                    have iid->left == at(before_parent_store, iid->left) by {
                                        preserve(memory(iid->left), loop(0).statement(5));
                                    }
                                    have iid->left == at(inner_inputs, iid->left) by {
                                        rewrite(iid->left, at(before_parent_store, iid->left));
                                        close();
                                    }
                                    have separate(loop(0).statement(5).footprint, memory(parent->left)) by {
                                        close() using { separate(memory(parent->right), memory(parent->left)); };
                                    }
                                    have parent->left == at(before_parent_store, parent->left) by {
                                        preserve(memory(parent->left), loop(0).statement(5));
                                    }
                                    have parent->left == at(inner_inputs, parent->left) by {
                                        rewrite(parent->left, at(before_parent_store, parent->left));
                                        close();
                                    }
                                    have separate(loop(0).statement(5).footprint, memory(sid->left)) by {
                                        close() using { separate(memory(parent->right), memory(sid->left)); };
                                    }
                                    have sid->left == at(before_parent_store, sid->left) by {
                                        preserve(memory(sid->left), loop(0).statement(5));
                                    }
                                    have sid->left == at(before_link_1, sid->left) by {
                                        rewrite(sid->left, at(before_parent_store, sid->left));
                                        close();
                                    }
                                    have separate(loop(0).statement(5).footprint, memory(iid->right)) by {
                                        close() using { separate(memory(parent->right), memory(iid->right)); };
                                    }
                                    have defined(iid->right) by {
                                        preserve(memory(iid->right), loop(0).statement(5));
                                    }
                                    have iid->right == at(before_parent_store, iid->right) by {
                                        preserve(memory(iid->right), loop(0).statement(5));
                                    }
                                    have parent->right == iid;
                                    have iid->right == sid;
                                    have sid->left == tmp1;
                                    // Only the parent's store lies between the retained_state and
                                    // this read of a different node's field.
                                    have sid->right == at(inner_inputs, sid->right) by close();
                                    let s = fold(tree(iid->right), { model: Tree::Node(sid, irm, srm), left: ir, right: sr });
                                    have iid->left == at(inner_inputs, iid->left) by close();
                                    let i = fold(tree(parent->right), { model: Tree::Node(iid, ilm, Tree::Node(sid, irm, srm)), left: il, right: s });
                                    let t = fold(tree(parent), { model: Tree::Node(id, lm, Tree::Node(iid, ilm, Tree::Node(sid, irm, srm))), left: l, right: i });
                                    step(); // Leave the loop.
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
pass
```
