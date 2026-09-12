# A theorem argument may be the null constant

The C null pointer constant stands at a pointer-typed theorem parameter and
lowers to that pointer type's null value, exactly as it does at a pure
function's pointer parameter
([`rb_pure_null_pointer_argument.md`](rb_pure_null_pointer_argument.md)). That
is what lets a whole-tree claim be stated at the null parent: the rbtree
model's `rb_tree_parent_consistent(t)` is `rb_parent_consistent(t, 0)`, and
lifting a per-step lemma over `p` to the whole tree applies it at `0`. Before
this rule `apply` refused the argument as an array reference that did not
evaluate to a pointer.

```c filename=null_theorem_argument.c
struct node { int value; struct node *left; };

int peek(struct node *p) {
    return p->value;
}
```

```click
verifying "null_theorem_argument.c";

spec enum Tree {
    Empty,
    Node(struct node*, Tree),
}

function parent_is(t: Tree, p: struct node*) -> int32 {
    match t {
        Tree::Empty => 1,
        Tree::Node(parent, left) => if parent == p { 1 } else { 0 },
    }
}

function tree_parent_is_null(t: Tree) -> int32 {
    parent_is(t, 0)
}

theorem parent_is_stable(t: Tree, p: struct node*) {
    ensures parent_is(t, p) == parent_is(t, p) by {
        normalize();
    }
}

theorem tree_parent_is_null_stable(t: Tree) {
    ensures parent_is(t, 0) == parent_is(t, 0) by {
        apply(parent_is_stable(t, 0));
        assumption();
    }
}

int peek(struct node* p) {
    requires p != 0;
    views p->value;
    ensures result == p->value;
} by {
    execute();
    simp();
}
```

```expect
pass
```
