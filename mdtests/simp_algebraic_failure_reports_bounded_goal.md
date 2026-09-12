# A failed pure `simp` reports a bounded goal, not a structure dump

A `simp` that cannot close a pure goal over algebraic values reports the goal
in its source vocabulary — constructors, pure function applications, and
typed binders — once, followed by the premises it had. The datatype's
instantiated schema graph is internal state and is never printed.

```click
spec enum Color {
    Red,
    Black,
}

spec enum RbTree {
    Empty,
    Node(int32, Color, RbTree, RbTree),
}

function color_bit(color: Color) -> int32 {
    match color {
        Color::Red => 0,
        Color::Black => 1,
    }
}

function root_color(tree: RbTree) -> Color {
    match tree {
        RbTree::Empty => Color::Black,
        RbTree::Node(value, color, left, right) => color,
    }
}

theorem color_bit_is_two(t: RbTree) {
    ensures color_bit(root_color(t)) == 2 and root_color(t) == Color::Red by {
        simp();
    }
}
```

```expect
fail: simplified proposition was not true: (int32 =(color_bit(root_color(v4000000:RbTree)), 2) is true ∧ root_color(v4000000:RbTree) = Color::Red)
  available pure facts: []
```
