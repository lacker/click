# recursive algebraic datatypes

Recursive fields are nominal references to the same finite datatype schema.
They do not expand the schema recursively. An unknown recursive value and the
recursive fields exposed by a match remain typed symbolic terms.

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

spec enum Tree<T> {
    Empty,
    Node(Tree<T>, T, Tree<T>),
}

spec enum EvenList<T> {
    EvenNil,
    EvenCons(T, OddList<T>),
}

spec enum OddList<T> {
    OddCons(T, EvenList<T>),
}

function tail_or_nil(xs: TestList<int32>) -> TestList<int32> {
    match xs {
        TestList::Nil => TestList<int32>::Nil,
        TestList::Cons(head, tail) => tail,
    }
}

function rebuild_list(xs: TestList<int32>) -> TestList<int32> {
    match xs {
        TestList::Nil => TestList<int32>::Nil,
        TestList::Cons(head, tail) => TestList<int32>::Cons(head, tail),
    }
}

function rebuild_tree(tree: Tree<int32>) -> Tree<int32> {
    match tree {
        Tree::Empty => Tree<int32>::Empty,
        Tree::Node(left, value, right) => Tree<int32>::Node(left, value, right),
    }
}

function rebuild_odd(xs: OddList<int32>) -> OddList<int32> {
    match xs {
        OddList::OddCons(head, tail) => OddList<int32>::OddCons(head, tail),
    }
}

theorem recursive_constructor_reduces(head: int32, tail: TestList<int32>) {
    ensures tail_or_nil(TestList<int32>::Cons(head, tail)) == tail by {
        unfold(tail_or_nil(TestList<int32>::Cons(head, tail)));
        simp();
    }
}

theorem recursive_symbolic_reconstruction(xs: TestList<int32>) {
    ensures rebuild_list(xs) == xs by {
        unfold(rebuild_list(xs));
        simp();
    }
}

theorem two_recursive_fields_reconstruct(tree: Tree<int32>) {
    ensures rebuild_tree(tree) == tree by {
        unfold(rebuild_tree(tree));
        simp();
    }
}

theorem mutually_recursive_fields_reconstruct(xs: OddList<int32>) {
    ensures rebuild_odd(xs) == xs by {
        unfold(rebuild_odd(xs));
        simp();
    }
}

theorem recursive_constructor_injectivity(
    head: int32,
    left: TestList<int32>,
    right: TestList<int32>
) {
    requires TestList<int32>::Cons(head, left) == TestList<int32>::Cons(head, right);
    ensures left == right by simp;
}
```

```expect
pass
```
