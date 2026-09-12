# a missed theorem premise is named, not dumped

`apply(theorem(args))` is a smart tactic: it selects the theorem's premises
from context by searching for a checked surface spelling of each one. The
search is bounded and it misses. Here it misses a pure fact about a model that
the `have` just above established, because the `have` proved it by rewriting
its goal through the arm's constructor and the form the search looks for is the
one written in the source.

A bounded smart-search miss is an ordinary outcome and the remedy is the simple
spelling, `apply(theorem(args)) using { P; ... }`, which checks exactly the
listed premises with no search — that is what
[`rb_insert_color.md`](rb_insert_color.md) writes for the same theorem.

What was not ordinary was the refusal. It printed the premise's Rust debug
form, which for a proposition over an algebraic model expands the complete
type, every variant, and the schema of every reachable type twice — about six
thousand characters naming nothing the author wrote. The premise is now
rendered the way a kernel goal is.

```c filename=parent_value.c
struct node {
    struct node *parent;
    int value;
};

int read_parent_value(struct node *n)
{
    struct node *p = n->parent;
    return 0;
}
```

```click
verifying "parent_value.c";

spec enum Tree {
    Empty,
    Node(struct node*, struct node*, int),
}

function parent_is(tree: Tree, q: struct node*) -> int32 {
    match tree {
        Tree::Empty => 0,
        Tree::Node(identity, parent, value) => if parent == q { 1 } else { 0 },
    }
}

theorem parent_is_holds(tree: Tree, q: struct node*) {
    requires parent_is(tree, q) == 1;

    ensures parent_is(tree, q) == 1 by { assumption(); }
}

resource tree_at(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(identity, parent, value) => {
            owns p->parent;
            owns p->value;
            fact p != 0;
            fact p == identity;
            fact p->parent == parent;
            fact p->value == value;
        },
    }
}

int read_parent_value(struct node* n) {
    consumes t: tree_at(n);
    requires t.model != Tree::Empty;
    produces u: tree_at(n);
    ensures result == 0;
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(identity, node_parent, value) => {
            have parent_is(t.model, node_parent) == 1 by {
                rewrite(t.model == Tree::Node(identity, node_parent, value));
                unfold(parent_is(Tree::Node(identity, node_parent, value), node_parent));
                normalize();
            }
            have parent_is(t.model, node_parent) == 1 by {
                apply(parent_is_holds(t.model, node_parent));
                assumption();
            }
            unfold(t);
            step();
            step();
            let u = fold(tree_at(n), { model: old(t.model) });
            execute();
            simp();
        },
    }
}
```

```expect
fail: theorem application `parent_is_holds` has no checked surface form for exact premise `int32 =(parent_is(
```
