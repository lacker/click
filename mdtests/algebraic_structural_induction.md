# structural induction over recursive algebraic values

Constructor-branching `induct` introduces one hypothesis for each immediate
recursive field. Constructor fields are scoped to their arm, and pure
functions remain symbolic until explicitly unfolded.

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

spec enum Tree<T> {
    Empty,
    Node(Tree<T>, T, Tree<T>),
}

function append(xs: TestList<int32>, ys: TestList<int32>) -> TestList<int32>
    decreases xs
{
    match xs {
        TestList::Nil => ys,
        TestList::Cons(head, tail) =>
            TestList<int32>::Cons(head, append(tail, ys)),
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

theorem append_right_identity(xs: TestList<int32>) {
    requires xs == xs;
    ensures append(xs, TestList<int32>::Nil) == xs by {
        induct(xs) as ih {
            TestList::Nil => {
                unfold(append(TestList<int32>::Nil, TestList<int32>::Nil));
                simp();
            }
            TestList::Cons(head, tail) => {
                apply(ih(tail));
                unfold(append(
                    TestList<int32>::Cons(head, tail),
                    TestList<int32>::Nil
                ));
                rewrite(append(tail, TestList<int32>::Nil) == tail);
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
