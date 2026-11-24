# solve does not evaluate a recursive function past an unknown argument

Evaluation unfolds only applications whose argument selects one arm of the
definition. With nothing known about `l`, `count(Tree::Node(v, l, r))` reduces
to `1 + count(l)` and stops there, so `solve` cannot show that it is `1`
(`mdtests/solve_evaluates_a_recursive_function_over_known_constructors.md`).

```click
spec enum Tree {
    Leaf,
    Node(int32, Tree, Tree),
}

function count(t: Tree) -> int32 decreases t {
    match t {
        Tree::Leaf => 0,
        Tree::Node(v, l, r) => 1 + count(l),
    }
}

theorem unknown_child(v: int32, l: Tree, r: Tree) {
    ensures count(Tree::Node(v, l, r)) == 1 by close();
}
```

```expect
fail: solve
```
