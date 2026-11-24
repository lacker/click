# A parent cast fact is not carried across a store through another node

`rb_parent(g)` recovers the parent from `g`'s parent-color word with an
integer-to-pointer cast. The cast result is named by the read of
`g->__rb_parent_color` it came from, and `node_at`'s fact
`((p->__rb_parent_color & ~3) as (struct rb_node *)) == parent` relates that read,
at the state where `n` was unfolded, to `parent`. Here `gp == xid`, so the
parent is `up_at`'s frame node, whose cells the function holds.

The store through `o` happens before the cast. A read is named by its state
and address without facts, so the cast's read after the store is a different
read from the one the unfolded fact names. Relating them would be frame
reasoning over the store, which term comparison does not do
(`docs/internals/verification-efficiency.md`). The cast result is then not
known to designate the held frame node, and forming `&p->rb_left` is refused.
[`a_parent_cast_restated_after_a_store_lets_the_parent_be_dereferenced.md`](a_parent_cast_restated_after_a_store_lets_the_parent_be_dereferenced.md)
restates the fact after the store and passes. The original is the
`__rb_rotate_set_parents` call in
`examples/rbtree/rbtree-insert/rbtree_insert.click`.

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));
static inline struct rb_node *rb_parent(struct rb_node *r) {
    return (struct rb_node *)(r->__rb_parent_color & ~3);
}
#endif
```

```c filename=a_parent_cast_fact_is_not_carried_across_a_store_through_another_node.c
#include "rbtree.h"

struct rb_node *peek(struct rb_node *g, struct rb_node *o) {
    o->__rb_parent_color = 0;
    struct rb_node *p = rb_parent(g);
    return p->rb_left;
}
```

```click
verifying "a_parent_cast_fact_is_not_carried_across_a_store_through_another_node.c";

spec enum Up {
    Frame(struct rb_node*, struct rb_node*),
}

spec enum Node {
    Inner(struct rb_node*, struct rb_node*),
}

function up_identity(u: Up) -> struct rb_node* {
    match u {
        Up::Frame(identity, child) => identity,
    }
}

function node_parent(n: Node) -> struct rb_node* {
    match n {
        Node::Inner(identity, parent) => parent,
    }
}

resource node_at(p: struct rb_node*) {
    field model: Node;
    match model {
        Node::Inner(identity, parent) => {
            owns p->__rb_parent_color;
            fact p != 0;
            fact p == identity;
            fact aligned(parent, 8);
            fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);
            fact ((p->__rb_parent_color & ~3) as (struct rb_node *)) == parent;
        },
    }
}

resource up_at(child: struct rb_node*) {
    field model: Up;
    match model {
        Up::Frame(identity, c) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            fact identity != 0;
            fact aligned(identity, 8);
            fact identity->rb_left == child;
        },
    }
}

struct rb_node* peek(struct rb_node* g, struct rb_node* o) {
    consumes n: node_at(g);
    consumes o->__rb_parent_color;
    consumes u: up_at(g);
    requires node_parent(n.model) == up_identity(u.model);
    ensures 1 == 1;
} by {
    match n.model {
        Node::Inner(gid, gp) => {
            match u.model {
                Up::Frame(xid, xc) => {
                    have node_parent(Node::Inner(gid, gp)) == gp by {
                        unfold(node_parent(Node::Inner(gid, gp)));
                        close();
                    }
                    have up_identity(Up::Frame(xid, xc)) == xid by {
                        unfold(up_identity(Up::Frame(xid, xc)));
                        close();
                    }
                    have gp == xid by {
                        rewrite(gp, node_parent(Node::Inner(gid, gp)));
                        rewrite(Node::Inner(gid, gp), n.model);
                        rewrite(xid, up_identity(Up::Frame(xid, xc)));
                        rewrite(Up::Frame(xid, xc), u.model);
                        close();
                    }
                    unfold(n);
                    unfold(u);
                    step();
                    step();
                    step();
                    step();
                    step();
                    close();
                },
            }
        },
    }
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
