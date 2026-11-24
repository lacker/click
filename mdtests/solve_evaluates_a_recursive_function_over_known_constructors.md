# solve evaluates a recursive function over known constructors

`solve` unfolds a recursive specification function applied to a known
constructor, then keeps unfolding the recursive calls the definition exposes,
to a fixed fuel (design-review P5, R3). An argument known only through an
equation such as `u == Tree::Node(..)` is rewritten to its constructor first.
Each unfold and rewrite is an ordinary checked step in the expansion.
Machine additions also need their domains proved. The nested example
establishes the inner calls first, so the outer unfold can prove that its
addition fits in `int32`.

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

theorem nested_constructors(v: int32, w: int32, r: Tree, s: Tree) {
    ensures count(Tree::Node(v, Tree::Node(w, Tree::Leaf, s), r)) == 2 by {
        have count(Tree::Leaf) == 0 by close();
        have count(Tree::Node(w, Tree::Leaf, s)) == 1 by close();
        close();
    };
}

theorem constructors_through_equations(t: Tree, u: Tree, v: int32, w: int32, r: Tree, s: Tree) {
    requires u == Tree::Node(w, Tree::Leaf, s);
    requires t == Tree::Node(v, u, r);
    ensures count(t) == 2 by close();
}

theorem an_unknown_tail_stays_folded(t: Tree, v: int32, l: Tree, r: Tree) {
    requires t == Tree::Node(v, l, r);
    requires count(l) == 3;
    ensures count(t) == 4 by close();
}
```

```expect
pass
```
