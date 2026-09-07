# recursive pure functions descend through algebraic fields

An algebraic datatype parameter can be a pure function's termination measure.
Recursive calls may use recursive fields exposed by matching that parameter.
Calls remain symbolic until an explicit one-layer `unfold`.

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
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

function list_length(xs: List<int32>) -> int32
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) => 1 + list_length(tail),
    }
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

function drop_pairs(xs: List<int32>) -> List<int32>
    decreases xs
{
    match xs {
        List::Nil => List<int32>::Nil,
        List::Cons(first, tail) => match tail {
            List::Nil => List<int32>::Nil,
            List::Cons(second, rest) => drop_pairs(rest),
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
    ensures list_length(List<int32>::Nil) == 0 by {
        unfold(list_length(List<int32>::Nil));
        simp();
    }
}

theorem cons_length_opens_one_layer(head: int32, tail: List<int32>) {
    ensures list_length(List<int32>::Cons(head, tail)) == 1 + list_length(tail) by {
        unfold(list_length(List<int32>::Cons(head, tail)));
        simp();
    }
}

theorem append_cons_opens_one_layer(
    head: int32,
    tail: List<int32>,
    ys: List<int32>
) {
    ensures append(List<int32>::Cons(head, tail), ys)
        == List<int32>::Cons(head, append(tail, ys)) by {
        unfold(append(List<int32>::Cons(head, tail), ys));
        simp();
    }
}

theorem nested_descent_opens_one_layer(
    first: int32,
    second: int32,
    rest: List<int32>
) {
    ensures drop_pairs(
        List<int32>::Cons(first, List<int32>::Cons(second, rest))
    ) == drop_pairs(rest) by {
        unfold(drop_pairs(
            List<int32>::Cons(first, List<int32>::Cons(second, rest))
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
