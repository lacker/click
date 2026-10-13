# `rb_next`'s `const` parameter and the cast that returns it

Linux declares `rb_next(const struct rb_node *node)` and returns the node its
descent reached as `(struct rb_node *)node`. The cast is how C says the caller
may write through a pointer the function itself only read through.

As in C, the result of an explicit cast has exactly the destination's pointee
qualification, so the unchanged signature and body are accepted. The rule is
documented in [the Supported C reference](../docs/reference/language/c.md);
[`c_const_cast_owned_write.md`](c_const_cast_owned_write.md) and
[`c_const_cast_storage_writes_rejected.md`](c_const_cast_storage_writes_rejected.md)
are its own regressions.

[`rb_next.md`](rb_next.md) still declares the parameter as
`struct rb_node *node`. Its proof was written against that signature and does
not go through unchanged with the `const` one, so this fixture pins only that
the unchanged translation unit is accepted. `rb_next.md` takes the `const`
back when its proof is adjusted.

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
#define NULL 0

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

#define rb_parent(r)   ((struct rb_node *)((r)->__rb_parent_color & ~3))

#define RB_EMPTY_NODE(node)  \
	((node)->__rb_parent_color == (unsigned long)(node))
#endif
```

```c filename=rb_next_const_signature.c
#include "rbtree.h"

struct rb_node *rb_next(const struct rb_node *node)
{
	struct rb_node *parent;

	if (RB_EMPTY_NODE(node))
		return NULL;

	/*
	 * If we have a right-hand child, go down and then left as far
	 * as we can.
	 */
	if (node->rb_right) {
		node = node->rb_right;
		while (node->rb_left)
			node = node->rb_left;
		return (struct rb_node *)node;
	}

	/*
	 * No right-hand children. Everything down and left is smaller than us,
	 * so any 'next' node must be in the general direction of our parent.
	 * Go up the tree; any time the ancestor is a right-hand child of its
	 * parent, keep going up. First time it's a left-hand child of its
	 * parent, said parent is our 'next' node.
	 */
	while ((parent = rb_parent(node)) && node == parent->rb_right)
		node = parent;

	return parent;
}
```

```click
verifying "rb_next_const_signature.c";
```

```expect
pass
```
