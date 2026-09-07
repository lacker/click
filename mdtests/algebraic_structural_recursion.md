# recursive pure functions descend through algebraic fields

An algebraic datatype parameter can be a pure function's termination measure.
Recursive calls may use recursive fields exposed by matching that parameter.
Calls remain symbolic until an explicit one-layer `unfold`.

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

function list_length(xs: TestList<int32>) -> int32
    decreases xs
{
    match xs {
        TestList::Nil => 0,
        TestList::Cons(head, tail) => 1 + list_length(tail),
    }
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

function drop_pairs(xs: TestList<int32>) -> TestList<int32>
    decreases xs
{
    match xs {
        TestList::Nil => TestList<int32>::Nil,
        TestList::Cons(first, tail) => match tail {
            TestList::Nil => TestList<int32>::Nil,
            TestList::Cons(second, rest) => drop_pairs(rest),
        },
    }
}

function tree_size(tree: Tree<int32>) -> int32
    decreases tree
{
    match tree {
        Tree::Empty => 0,
        Tree::Node(left, value, right) =>
            1 + tree_size(left) + tree_size(right),
    }
}

function even_length(xs: EvenList<int32>) -> int32
    decreases xs
{
    match xs {
        EvenList::EvenNil => 0,
        EvenList::EvenCons(head, tail) => 1 + odd_length(tail),
    }
}

function odd_length(xs: OddList<int32>) -> int32
    decreases xs
{
    match xs {
        OddList::OddCons(head, tail) => 1 + even_length(tail),
    }
}

theorem empty_length_is_zero() {
    ensures list_length(TestList<int32>::Nil) == 0 by {
        unfold(list_length(TestList<int32>::Nil));
        simp();
    }
}

theorem cons_length_opens_one_layer(head: int32, tail: TestList<int32>) {
    ensures list_length(TestList<int32>::Cons(head, tail)) == 1 + list_length(tail) by {
        unfold(list_length(TestList<int32>::Cons(head, tail)));
        simp();
    }
}

theorem append_cons_opens_one_layer(
    head: int32,
    tail: TestList<int32>,
    ys: TestList<int32>
) {
    ensures append(TestList<int32>::Cons(head, tail), ys)
        == TestList<int32>::Cons(head, append(tail, ys)) by {
        unfold(append(TestList<int32>::Cons(head, tail), ys));
        simp();
    }
}

theorem nested_descent_opens_one_layer(
    first: int32,
    second: int32,
    rest: TestList<int32>
) {
    ensures drop_pairs(
        TestList<int32>::Cons(first, TestList<int32>::Cons(second, rest))
    ) == drop_pairs(rest) by {
        unfold(drop_pairs(
            TestList<int32>::Cons(first, TestList<int32>::Cons(second, rest))
        ));
        simp();
    }
}

theorem tree_recursion_opens_both_children(
    left: Tree<int32>,
    value: int32,
    right: Tree<int32>
) {
    ensures tree_size(Tree<int32>::Node(left, value, right))
        == 1 + tree_size(left) + tree_size(right) by {
        unfold(tree_size(Tree<int32>::Node(left, value, right)));
        simp();
    }
}

theorem mutual_recursion_opens_one_layer(
    head: int32,
    tail: OddList<int32>
) {
    ensures even_length(EvenList<int32>::EvenCons(head, tail))
        == 1 + odd_length(tail) by {
        unfold(even_length(EvenList<int32>::EvenCons(head, tail)));
        simp();
    }
}
```

```expect
pass
```
