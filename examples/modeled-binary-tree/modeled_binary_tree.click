verifying "modeled_binary_tree.c";

spec enum HeapTree {
    Empty,
    Node(struct tree_node*, int, HeapTree, HeapTree),
}

resource tree_at(p: struct tree_node*) {
    field model: HeapTree;
    match model {
        HeapTree::Empty => { fact p == 0; },
        HeapTree::Node(identity, value, left_model, right_model) => {
            owns p->value;
            owns p->left;
            owns p->right;
            owns left: tree_at(p->left);
            owns right: tree_at(p->right);
            fact p != 0;
            fact p == identity;
            fact p->value == value;
            fact left.model == left_model;
            fact right.model == right_model;
        },
    }
}

void tree_node_init(struct tree_node* node, int value,
                    struct tree_node* left, struct tree_node* right) {
    consumes node->value;
    consumes node->left;
    consumes node->right;
    consumes l: tree_at(left);
    consumes r: tree_at(right);
    requires node != 0;
    produces root: tree_at(node);
    ensures root.model == HeapTree::Node(node, value, old(l.model), old(r.model));
} by {
    execute();
    let root = fold(tree_at(node), {
        model: HeapTree::Node(node, value, l.model, r.model)
    }, { left: l, right: r });
    simp();
}

function heap_right(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => right,
    }
}

function heap_rotate_left(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => match right {
            HeapTree::Empty => tree,
            HeapTree::Node(pivot_node, pivot_value, middle, far_right) =>
                HeapTree::Node(pivot_node, pivot_value,
                    HeapTree::Node(node, value, left, middle), far_right),
        },
    }
}

function heap_inorder(tree: HeapTree) -> List<struct tree_node*>
    decreases tree
{
    match tree {
        HeapTree::Empty => List<struct tree_node*>::Nil,
        HeapTree::Node(node, value, left, right) =>
            list_append(heap_inorder(left), List<struct tree_node*>::Cons(node, heap_inorder(right))),
    }
}

theorem heap_rotate_left_node_preserves_inorder(node: struct tree_node*, value: int,
                                               left: HeapTree, right: HeapTree) {
    ensures heap_inorder(heap_rotate_left(HeapTree::Node(node, value, left, right)))
        == heap_inorder(HeapTree::Node(node, value, left, right)) by {
        induct(right) as ih {
            HeapTree::Empty => {
                unfold(heap_rotate_left(HeapTree::Node(node, value, left, HeapTree::Empty)));
                normalize();
            }
            HeapTree::Node(pivot, pivot_value, middle, far_right) => {
                unfold(heap_rotate_left(HeapTree::Node(node, value, left,
                    HeapTree::Node(pivot, pivot_value, middle, far_right))));
                unfold(heap_inorder(HeapTree::Node(pivot, pivot_value,
                    HeapTree::Node(node, value, left, middle), far_right)));
                unfold(heap_inorder(HeapTree::Node(node, value, left,
                    HeapTree::Node(pivot, pivot_value, middle, far_right))));
                unfold(heap_inorder(HeapTree::Node(node, value, left, middle)));
                unfold(heap_inorder(HeapTree::Node(pivot, pivot_value, middle, far_right)));
                apply(list_append_associative(heap_inorder(left),
                    List<struct tree_node*>::Cons(node, heap_inorder(middle)),
                    List<struct tree_node*>::Cons(pivot, heap_inorder(far_right))));
                rewrite(list_append(list_append(heap_inorder(left),
                    List<struct tree_node*>::Cons(node, heap_inorder(middle))),
                    List<struct tree_node*>::Cons(pivot, heap_inorder(far_right)))
                    == list_append(heap_inorder(left),
                        list_append(List<struct tree_node*>::Cons(node, heap_inorder(middle)),
                            List<struct tree_node*>::Cons(pivot, heap_inorder(far_right)))));
                unfold(list_append(List<struct tree_node*>::Cons(node, heap_inorder(middle)),
                    List<struct tree_node*>::Cons(pivot, heap_inorder(far_right))));
                normalize();
            }
        }
    }
}

theorem heap_rotate_left_preserves_inorder(tree: HeapTree) {
    ensures heap_inorder(heap_rotate_left(tree)) == heap_inorder(tree) by {
        induct(tree) as ih {
            HeapTree::Empty => {
                unfold(heap_rotate_left(HeapTree::Empty));
                normalize();
            }
            HeapTree::Node(node, value, left, right) => {
                apply(heap_rotate_left_node_preserves_inorder(node, value, left, right));
                assumption();
            }
        }
    }
}

struct tree_node* tree_rotate_left(struct tree_node* root) {
    consumes t: tree_at(root);
    requires t.model != HeapTree::Empty;
    requires heap_right(t.model) != HeapTree::Empty;
    produces rotated: tree_at(result);
    ensures rotated.model == heap_rotate_left(old(t.model));
    ensures heap_inorder(rotated.model) == heap_inorder(old(t.model));
} by {
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(node, value, left_model, right_model) => {
            have heap_right(t.model) == right_model by {
                rewrite(t.model == HeapTree::Node(node, value, left_model, right_model));
                unfold(heap_right(HeapTree::Node(node, value, left_model, right_model)));
                normalize();
            }
            have right_model != HeapTree::Empty by {
                rewrite(right_model == heap_right(t.model));
                assumption();
            }
            match right_model {
                HeapTree::Empty => { contradiction(right_model == HeapTree::Empty); },
                HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model) => {
                    unfold(t) as { left: l, right: r };
                    unfold(r) as { left: m, right: z };
                    execute();
                    let lower = fold(tree_at(root), {
                        model: HeapTree::Node(node, value, left_model, middle_model)
                    }, { left: l, right: m });
                    let rotated = fold(tree_at(result), {
                        model: HeapTree::Node(pivot_node, pivot_value,
                            HeapTree::Node(node, value, left_model, middle_model), far_right_model)
                    }, { left: lower, right: z });
                    have rotated.model == heap_rotate_left(old(t.model)) by {
                        rewrite(old(t.model) == HeapTree::Node(node, value, left_model, right_model));
                        rewrite(right_model == HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model));
                        unfold(heap_rotate_left(HeapTree::Node(node, value, left_model,
                            HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model))));
                        normalize();
                    }
                    have heap_inorder(rotated.model) == heap_inorder(old(t.model)) by {
                        rewrite(rotated.model == heap_rotate_left(old(t.model)));
                        apply(heap_rotate_left_preserves_inorder(old(t.model)));
                        assumption();
                    }
                    simp();
                },
            }
        },
    }
}

spec enum Tree<T> {
    Empty,
    Node(Tree<T>, T, Tree<T>),
}

function tree_size<T>(tree: Tree<T>) -> Nat
    decreases tree
{
    match tree {
        Tree::Empty => Nat::Zero,
        Tree::Node(left, value, right) =>
            Nat::Succ(nat_add(tree_size(left), tree_size(right))),
    }
}

function tree_mirror<T>(tree: Tree<T>) -> Tree<T>
    decreases tree
{
    match tree {
        Tree::Empty => Tree<T>::Empty,
        Tree::Node(left, value, right) =>
            Tree<T>::Node(tree_mirror(right), value, tree_mirror(left)),
    }
}

theorem tree_mirror_twice<T>(tree: Tree<T>) {
    ensures tree_mirror(tree_mirror(tree)) == tree by {
        induct(tree) as ih {
            Tree::Empty => {
                unfold(tree_mirror(Tree<T>::Empty));
                simp();
            }
            Tree::Node(left, value, right) => {
                apply(ih(left));
                apply(ih(right));
                unfold(tree_mirror(Tree<T>::Node(left, value, right)));
                unfold(tree_mirror(Tree<T>::Node(tree_mirror(right), value, tree_mirror(left))));
                rewrite(tree_mirror(tree_mirror(left)) == left);
                rewrite(tree_mirror(tree_mirror(right)) == right);
                normalize();
            }
        }
    }
}

theorem tree_mirror_preserves_size<T>(tree: Tree<T>) {
    ensures tree_size(tree_mirror(tree)) == tree_size(tree) by {
        induct(tree) as ih {
            Tree::Empty => {
                unfold(tree_mirror(Tree<T>::Empty));
                normalize();
            }
            Tree::Node(left, value, right) => {
                apply(ih(left));
                apply(ih(right));
                unfold(tree_mirror(Tree<T>::Node(left, value, right)));
                unfold(tree_size(Tree<T>::Node(tree_mirror(right), value, tree_mirror(left))));
                unfold(tree_size(Tree<T>::Node(left, value, right)));
                rewrite(tree_size(tree_mirror(left)) == tree_size(left));
                rewrite(tree_size(tree_mirror(right)) == tree_size(right));
                apply(nat_add_commutative(tree_size(right), tree_size(left)));
                rewrite(nat_add(tree_size(right), tree_size(left))
                    == nat_add(tree_size(left), tree_size(right)));
                normalize();
            }
        }
    }
}
