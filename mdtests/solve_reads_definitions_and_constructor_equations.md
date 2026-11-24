# `solve` reads a definition's condition and joins constructor equations

Reading a condition out of a function's definition, and joining two
constructor equations of one value, are strategies of `solve` over the facts
connected to the goal, so `close()` proves what the omitted proof does in
[`solve_reads_a_condition_out_of_a_definition.md`](solve_reads_a_condition_out_of_a_definition.md)
and
[`solve_reads_fields_through_two_constructor_equations.md`](solve_reads_fields_through_two_constructor_equations.md).

```click
spec enum Tree {
    Leaf,
    Node(int, Tree, Tree),
}

function balanced(tree: Tree) -> int
    decreases tree
{
    match tree {
        Tree::Leaf => 1,
        Tree::Node(value, left, right) =>
            if balanced(left) == 1 {
                if balanced(right) == 1 { 1 } else { 0 }
            } else {
                0
            },
    }
}

theorem left_balanced(value: int, left: Tree, right: Tree) {
    requires balanced(Tree::Node(value, left, right)) == 1;
    ensures balanced(left) == 1 by close();
}

spec enum Color { Red, Black }
spec enum Pair { Empty, Node(Color, Pair) }

theorem first_field(t: Pair, c: Color, r: Pair) {
    requires t == Pair::Node(c, r);
    requires t == Pair::Node(Color::Black, Pair::Empty);
    ensures c == Color::Black by close();
}

theorem different_constructors(t: Pair, c: Color, r: Pair) {
    requires t == Pair::Node(c, r);
    requires t == Pair::Empty;
    ensures c == Color::Red by close();
}
```

```expect
pass
```
