verifying "modeled_binary_tree.c";

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
