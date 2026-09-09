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
