# A loop cursor needs its owner alias before reading a folded child

```c filename=loop-cursor-model-pointer-read.c
struct node { uint64 tag; struct node *right; struct node *left; };
void inspect(struct node *root) {
    struct node *parent = root;
    struct node *child;
    while (true) {
        child = parent->left;
        parent = child;
        break;
    }
}
```

```click
verifying "loop-cursor-model-pointer-read.c";
spec enum Identity { At(struct node*) }
spec enum Parent { At(struct node*, Identity) }
resource cell(p: struct node*) {
    field model: Identity;
    match model {
        Identity::At(identity) => { owns p->tag; fact p == identity; },
    }
}
resource parent_at(p: struct node*) {
    field model: Parent;
    match model {
        Parent::At(identity, child_model) => {
            owns p->left;
            fact p == identity;
            owns child: cell(p->left);
            fact child.model == child_model;
        },
    }
}
void inspect(struct node* root) {
    owns tree: parent_at(root);
    ensures 1 == 1;
} by {
    step_until(loop(0).entry);
    loop {
        owns tree: parent_at(root);
        decreases 0;
        initialize by close();
        maintain by {
            match tree.model {
                Parent::At(pid, child_model) => {
                    let { child: sub } = unfold(tree);
                    match sub.model {
                        Identity::At(sid) => {
                            unfold(sub);
                            step();
                            have child == sid;
                            let sub = fold(cell(root->left), { model: Identity::At(sid) });
                            let tree = fold(parent_at(root), { model: Parent::At(pid, Identity::At(sid)), child: sub });
                            step(); step();
                        },
                    }
                },
            }
        }
    }
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
