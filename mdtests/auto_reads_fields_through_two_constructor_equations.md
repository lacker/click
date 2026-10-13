# `auto` reads fields through two constructor equations

Two facts can equate the same value to constructor applications: a `match`
arm says `t.model == Tree::Node(color)`, and a requirement says
`t.model == Tree::Node(Color::Black)`. Neither fact alone says
`color == Color::Black`. `auto` states the equation between the two
applications, proved by rewriting each to the shared value, and `simp` then
reads the fields' equality from it. Different constructors make the same
equation a contradiction.

```c filename=auto_reads_fields_through_two_constructor_equations.c
struct node { unsigned long bits; };

void touch(struct node *p) {
}
```

```click
verifying "auto_reads_fields_through_two_constructor_equations.c";

spec enum Color { Red, Black }
spec enum Tree { Empty, Node(Color, Tree) }

theorem first_field(t: Tree, c: Color, r: Tree) {
    requires t == Tree::Node(c, r);
    requires t == Tree::Node(Color::Black, Tree::Empty);
    ensures c == Color::Black by auto;
}

theorem second_field(t: Tree, c: Color, r: Tree) {
    requires t == Tree::Node(c, r);
    requires t == Tree::Node(Color::Black, Tree::Empty);
    ensures r == Tree::Empty by auto;
}

theorem different_constructors(t: Tree, c: Color, r: Tree) {
    requires t == Tree::Node(c, r);
    requires t == Tree::Empty;
    ensures c == Color::Red by auto;
}

resource at(p: struct node*) {
    field model: Tree;
    owns p->bits;
}

void touch(struct node *p) {
    owns t: at(p);
    requires t.model != Tree::Empty;
    requires t.model == Tree::Node(Color::Black, Tree::Empty);
    ensures t.model == Tree::Node(Color::Black, Tree::Empty);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(color, rest) => {
            have color == Color::Black by auto;
            execute();
        }
    }
}
```

```expect
pass
```
