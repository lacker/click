# structural induction over recursive algebraic values

Constructor-branching `induct` introduces one hypothesis for each immediate
recursive field. Constructor fields are scoped to their arm, and pure
functions remain symbolic until explicitly unfolded.

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}

spec enum Tree<T> {
    Empty,
    Node(Tree<T>, T, Tree<T>),
}

function append(xs: List<int32>, ys: List<int32>) -> List<int32>
    decreases xs
{
    match xs {
        List::Nil => ys,
        List::Cons(head, tail) =>
            List<int32>::Cons(head, append(tail, ys)),
    }
}

function copy_tree(tree: Tree<int32>) -> Tree<int32>
    decreases tree
{
    match tree {
        Tree::Empty => Tree<int32>::Empty,
        Tree::Node(left, value, right) => Tree<int32>::Node(
            copy_tree(left),
            value,
            copy_tree(right)
        ),
    }
}

theorem append_right_identity(xs: List<int32>) {
    requires xs == xs;
    ensures append(xs, List<int32>::Nil) == xs by {
        induct(xs) as ih {
            List::Nil => {
                unfold(append(List<int32>::Nil, List<int32>::Nil));
                simp();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                unfold(append(
                    List<int32>::Cons(head, tail),
                    List<int32>::Nil
                ));
                rewrite(append(tail, List<int32>::Nil) == tail);
                normalize();
            }
        }
    }
}

theorem copy_tree_identity(tree: Tree<int32>) {
    ensures copy_tree(tree) == tree by {
        induct(tree) as ih {
            Tree::Empty => {
                unfold(copy_tree(Tree<int32>::Empty));
                simp();
            }
            Tree::Node(left, value, right) => {
                apply(ih(left));
                apply(ih(right));
                unfold(copy_tree(Tree<int32>::Node(left, value, right)));
                rewrite(copy_tree(left) == left);
                rewrite(copy_tree(right) == right);
                normalize();
            }
        }
    }
}
```

```expect
pass
```
