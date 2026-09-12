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

function heap_left(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => left,
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

function heap_rotate_right(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => match left {
            HeapTree::Empty => tree,
            HeapTree::Node(pivot_node, pivot_value, far_left, middle) =>
                HeapTree::Node(pivot_node, pivot_value, far_left,
                    HeapTree::Node(node, value, middle, right)),
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

function heap_member(tree: HeapTree, target: struct tree_node*) -> int32
    decreases tree
{
    match tree {
        HeapTree::Empty => 0,
        HeapTree::Node(node, value, left, right) =>
            if node == target {
                1
            } else {
                if heap_member(left, target) == 1 {
                    1
                } else {
                    heap_member(right, target)
                }
            },
    }
}

theorem heap_member_nonzero_is_one(tree: HeapTree, target: struct tree_node*) {
    ensures heap_member(tree, target) != 0 implies heap_member(tree, target) == 1 by {
        induct(tree) as ih {
            HeapTree::Empty => {
                intro();
                have heap_member(HeapTree::Empty, target) == 0 by {
                    unfold(heap_member(HeapTree::Empty, target));
                    normalize();
                }
                contradiction(heap_member(HeapTree::Empty, target) == 0);
            }
            HeapTree::Node(node, value, left, right) => {
                intro();
                if node == target {
                    have heap_member(HeapTree::Node(node, value, left, right), target) == 1 by {
                        unfold(heap_member(
                            HeapTree::Node(node, value, left, right), target));
                        normalize() using { node == target; }
                    }
                    assumption();
                } else {
                    if heap_member(left, target) == 0 {
                        have heap_member(right, target)
                            == heap_member(HeapTree::Node(node, value, left, right), target) by {
                            unfold(heap_member(
                                HeapTree::Node(node, value, left, right), target));
                            rewrite(heap_member(left, target) == 0);
                            normalize() using { not(node == target); }
                        }
                        have heap_member(HeapTree::Node(node, value, left, right), target)
                            == heap_member(right, target) by {
                            unfold(heap_member(
                                HeapTree::Node(node, value, left, right), target));
                            rewrite(heap_member(left, target) == 0);
                            normalize() using { not(node == target); }
                        }
                        have heap_member(right, target) != 0 by {
                            rewrite(heap_member(right, target)
                                == heap_member(HeapTree::Node(node, value, left, right), target));
                            assumption();
                        }
                        apply(ih(right));
                        extract(heap_member(right, target) == 1);
                        have heap_member(HeapTree::Node(node, value, left, right), target) == 1 by {
                            rewrite(heap_member(HeapTree::Node(node, value, left, right), target)
                                == heap_member(right, target));
                            assumption();
                        }
                        assumption();
                    } else {
                        apply(ih(left));
                        extract(heap_member(left, target) == 1);
                        have heap_member(HeapTree::Node(node, value, left, right), target) == 1 by {
                            unfold(heap_member(
                                HeapTree::Node(node, value, left, right), target));
                            rewrite(heap_member(left, target) == 1);
                            normalize() using { not(node == target); }
                        }
                        assumption();
                    }
                }
            }
        }
    }
}

theorem heap_member_is_inorder_membership(tree: HeapTree, target: struct tree_node*) {
    ensures heap_member(tree, target) == list_contains(heap_inorder(tree), target) by {
        induct(tree) as ih {
            HeapTree::Empty => {
                unfold(heap_member(HeapTree::Empty, target));
                unfold(heap_inorder(HeapTree::Empty));
                unfold(list_contains(List<struct tree_node*>::Nil, target));
                normalize();
            }
            HeapTree::Node(node, value, left, right) => {
                apply(ih(left));
                apply(ih(right));
                unfold(heap_member(HeapTree::Node(node, value, left, right), target));
                unfold(heap_inorder(HeapTree::Node(node, value, left, right)));
                apply(list_contains_append(heap_inorder(left),
                    List<struct tree_node*>::Cons(node, heap_inorder(right)), target));
                rewrite(list_contains(list_append(heap_inorder(left),
                    List<struct tree_node*>::Cons(node, heap_inorder(right))), target)
                    == if list_contains(heap_inorder(left), target) == 1 {
                        1
                    } else {
                        list_contains(List<struct tree_node*>::Cons(node, heap_inorder(right)), target)
                    });
                apply(list_contains_cons(node, heap_inorder(right), target));
                rewrite(list_contains(List<struct tree_node*>::Cons(node, heap_inorder(right)), target)
                    == if node == target {
                        1
                    } else {
                        list_contains(heap_inorder(right), target)
                    });
                rewrite(heap_member(left, target) == list_contains(heap_inorder(left), target));
                rewrite(heap_member(right, target) == list_contains(heap_inorder(right), target));
                if node == target {
                    normalize() using { node == target; }
                } else {
                    normalize() using { not(node == target); }
                }
            }
        }
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

theorem heap_rotate_right_node_preserves_inorder(node: struct tree_node*, value: int,
                                                 left: HeapTree, right: HeapTree) {
    ensures heap_inorder(heap_rotate_right(HeapTree::Node(node, value, left, right)))
        == heap_inorder(HeapTree::Node(node, value, left, right)) by {
        induct(left) as ih {
            HeapTree::Empty => {
                unfold(heap_rotate_right(HeapTree::Node(node, value, HeapTree::Empty, right)));
                normalize();
            }
            HeapTree::Node(pivot, pivot_value, far_left, middle) => {
                unfold(heap_rotate_right(HeapTree::Node(node, value,
                    HeapTree::Node(pivot, pivot_value, far_left, middle), right)));
                unfold(heap_inorder(HeapTree::Node(pivot, pivot_value, far_left,
                    HeapTree::Node(node, value, middle, right))));
                unfold(heap_inorder(HeapTree::Node(node, value,
                    HeapTree::Node(pivot, pivot_value, far_left, middle), right)));
                unfold(heap_inorder(HeapTree::Node(node, value, middle, right)));
                unfold(heap_inorder(HeapTree::Node(pivot, pivot_value, far_left, middle)));
                apply(list_append_associative(heap_inorder(far_left),
                    List<struct tree_node*>::Cons(pivot, heap_inorder(middle)),
                    List<struct tree_node*>::Cons(node, heap_inorder(right))));
                rewrite(list_append(list_append(heap_inorder(far_left),
                    List<struct tree_node*>::Cons(pivot, heap_inorder(middle))),
                    List<struct tree_node*>::Cons(node, heap_inorder(right)))
                    == list_append(heap_inorder(far_left),
                        list_append(List<struct tree_node*>::Cons(pivot, heap_inorder(middle)),
                            List<struct tree_node*>::Cons(node, heap_inorder(right)))));
                unfold(list_append(List<struct tree_node*>::Cons(pivot, heap_inorder(middle)),
                    List<struct tree_node*>::Cons(node, heap_inorder(right))));
                normalize();
            }
        }
    }
}

theorem heap_rotate_right_preserves_inorder(tree: HeapTree) {
    ensures heap_inorder(heap_rotate_right(tree)) == heap_inorder(tree) by {
        induct(tree) as ih {
            HeapTree::Empty => {
                unfold(heap_rotate_right(HeapTree::Empty));
                normalize();
            }
            HeapTree::Node(node, value, left, right) => {
                apply(heap_rotate_right_node_preserves_inorder(node, value, left, right));
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

struct tree_node* tree_rotate_right(struct tree_node* root) {
    consumes t: tree_at(root);
    requires t.model != HeapTree::Empty;
    requires heap_left(t.model) != HeapTree::Empty;
    produces rotated: tree_at(result);
    ensures rotated.model == heap_rotate_right(old(t.model));
    ensures heap_inorder(rotated.model) == heap_inorder(old(t.model));
} by {
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(node, value, left_model, right_model) => {
            have heap_left(t.model) == left_model by {
                rewrite(t.model == HeapTree::Node(node, value, left_model, right_model));
                unfold(heap_left(HeapTree::Node(node, value, left_model, right_model)));
                normalize();
            }
            have left_model != HeapTree::Empty by {
                rewrite(left_model == heap_left(t.model));
                assumption();
            }
            match left_model {
                HeapTree::Empty => { contradiction(left_model == HeapTree::Empty); },
                HeapTree::Node(pivot_node, pivot_value, far_left_model, middle_model) => {
                    unfold(t) as { left: l, right: r };
                    unfold(l) as { left: z, right: m };
                    execute();
                    let lower = fold(tree_at(root), {
                        model: HeapTree::Node(node, value, middle_model, right_model)
                    }, { left: m, right: r });
                    let rotated = fold(tree_at(result), {
                        model: HeapTree::Node(pivot_node, pivot_value, far_left_model,
                            HeapTree::Node(node, value, middle_model, right_model))
                    }, { left: z, right: lower });
                    have rotated.model == heap_rotate_right(old(t.model)) by {
                        rewrite(old(t.model) == HeapTree::Node(node, value, left_model, right_model));
                        rewrite(left_model == HeapTree::Node(pivot_node, pivot_value, far_left_model, middle_model));
                        unfold(heap_rotate_right(HeapTree::Node(node, value,
                            HeapTree::Node(pivot_node, pivot_value, far_left_model, middle_model), right_model)));
                        normalize();
                    }
                    have heap_inorder(rotated.model) == heap_inorder(old(t.model)) by {
                        rewrite(rotated.model == heap_rotate_right(old(t.model)));
                        apply(heap_rotate_right_preserves_inorder(old(t.model)));
                        assumption();
                    }
                    simp();
                },
            }
        },
    }
}

int tree_contains(struct tree_node* root, struct tree_node* target) {
    owns t: tree_at(root);
    ensures t.model == old(t.model);
    ensures result == heap_member(old(t.model), target);
} by {
    match t.model {
        HeapTree::Empty => {
            unfold(t);
            execute();
            let t = fold(tree_at(root), { model: HeapTree::Empty });
            have result == heap_member(old(t.model), target) by {
                rewrite(old(t.model) == HeapTree::Empty);
                unfold(heap_member(HeapTree::Empty, target));
                normalize();
            }
            simp();
        },
        HeapTree::Node(node, value, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            branch {
                then { step(); simp(); }
                else {}
            }
            branch {
                then {
                    step();
                    let t = fold(tree_at(root), { model: old(t.model) }, { left: l, right: r });
                    have node == target by {
                        rewrite(node == root);
                        normalize() using { root == target; }
                    }
                    have result == heap_member(old(t.model), target) by {
                        rewrite(old(t.model)
                            == HeapTree::Node(node, value, left_model, right_model));
                        unfold(heap_member(
                            HeapTree::Node(node, value, left_model, right_model), target));
                        normalize() using { node == target; }
                    }
                    simp();
                }
                else {}
            }
            have not(node == target) by {
                rewrite(node == root);
                normalize() using { not(root == target); }
            }
            let found_left = step(tree_contains(root->left, target), { t: l });
            branch {
                then {
                    step();
                    have heap_member(left_model, target) == 1 by {
                        have heap_member(left_model, target) != 0 by {
                            simp() using {
                                found_left != 0;
                                found_left == heap_member(left_model, target);
                            }
                        }
                        have left_model == l.model by {
                            rewrite(l.model == left_model);
                            normalize();
                        }
                        have heap_member(l.model, target) != 0 by {
                            rewrite(l.model == left_model);
                            assumption();
                        }
                        apply(heap_member_nonzero_is_one(l.model, target));
                        extract(heap_member(l.model, target) == 1);
                        rewrite(left_model == l.model);
                        assumption();
                    }
                    let t = fold(tree_at(root), { model: old(t.model) }, { left: l, right: r });
                    have result == heap_member(old(t.model), target) by {
                        rewrite(old(t.model)
                            == HeapTree::Node(node, value, left_model, right_model));
                        unfold(heap_member(
                            HeapTree::Node(node, value, left_model, right_model), target));
                        rewrite(heap_member(left_model, target) == 1);
                        normalize() using { not(node == target); }
                    }
                    simp();
                }
                else {}
            }
            have heap_member(left_model, target) == 0 by {
                simp() using {
                    found_left == 0;
                    found_left == heap_member(left_model, target);
                }
            }
            let found_right = step(tree_contains(root->right, target), { t: r });
            step();
            let t = fold(tree_at(root), { model: old(t.model) }, { left: l, right: r });
            have result == heap_member(right_model, target) by {
                rewrite(found_right == heap_member(right_model, target));
                normalize();
            }
            have result == heap_member(old(t.model), target) by {
                rewrite(old(t.model)
                    == HeapTree::Node(node, value, left_model, right_model));
                unfold(heap_member(
                    HeapTree::Node(node, value, left_model, right_model), target));
                rewrite(heap_member(left_model, target) == 0);
                rewrite(result == heap_member(right_model, target));
                normalize() using { not(node == target); }
            }
            simp();
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
