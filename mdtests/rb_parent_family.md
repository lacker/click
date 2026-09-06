# rbtree parent-color helpers recover provenance through a tagged word

The `rb_node` word packs a parent pointer and one color bit. The header
carries the Linux helper shapes unchanged; each contracted caller states the
word's form with `address(parent)` and the color, and the kernel recovers the
parent with its provenance.

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
#define NULL 0
#define RB_RED 0
#define RB_BLACK 1

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

static inline struct rb_node *rb_parent(struct rb_node *r) {
    return (struct rb_node *)(r->__rb_parent_color & ~3);
}

static inline unsigned long rb_color(struct rb_node *rb) {
    return rb->__rb_parent_color & 1;
}

static inline void rb_set_parent(struct rb_node *rb, struct rb_node *p) {
    rb->__rb_parent_color = rb_color(rb) | (unsigned long)p;
}

static inline void rb_set_parent_color(struct rb_node *rb, struct rb_node *p, int32 color) {
    rb->__rb_parent_color = (unsigned long)p | color;
}

static inline struct rb_node *rb_red_parent(struct rb_node *red) {
    return (struct rb_node *)red->__rb_parent_color;
}

static inline int32 rb_empty_node(struct rb_node *node) {
    return node->__rb_parent_color == (unsigned long)node;
}

static inline void rb_clear_node(struct rb_node *node) {
    node->__rb_parent_color = (unsigned long)node;
}

static inline void rb_link_node(struct rb_node *node, struct rb_node *parent,
                                struct rb_node **rb_link) {
    node->__rb_parent_color = (unsigned long)parent;
    node->rb_left = NULL;
    node->rb_right = NULL;
    *rb_link = node;
}
#endif
```

```c filename=rb_parent_family.c
#include "rbtree.h"

struct rb_node *parent_of(struct rb_node *node) {
    return rb_parent(node);
}

unsigned long color_of(struct rb_node *node) {
    return rb_color(node);
}

void set_parent(struct rb_node *node, struct rb_node *parent) {
    rb_set_parent(node, parent);
}

void set_black_parent(struct rb_node *node, struct rb_node *parent) {
    rb_set_parent_color(node, parent, RB_BLACK);
}

struct rb_node *detach_black(struct rb_node *node) {
    rb_set_parent_color(node, NULL, RB_BLACK);
    return rb_parent(node);
}

struct rb_node *red_parent_of(struct rb_node *red) {
    return rb_red_parent(red);
}

int32 cleared_is_empty(struct rb_node *node) {
    rb_clear_node(node);
    return rb_empty_node(node);
}

int32 relinked_is_empty(struct rb_node *node, struct rb_node *parent) {
    rb_set_parent(node, parent);
    return rb_empty_node(node);
}

void link_node(struct rb_node *node, struct rb_node *parent, struct rb_node **rb_link) {
    rb_link_node(node, parent, rb_link);
}
```

```click
resource linked(node: struct rb_node*) {
    owns node->__rb_parent_color;
    fact aligned(node, 8);
    let parent: struct rb_node* where aligned(parent, 8) and
        node->__rb_parent_color == address(parent) + (node->__rb_parent_color & 1);
}

verifying "rb_parent_family.c";

struct rb_node* parent_of(struct rb_node* node) {
    requires node != 0;
    owns linked(node);
    ensures address(result) == (node->__rb_parent_color & ~3);
} by {
    unfold(linked(node));
    execute();
    fold(linked(node));
    simp();
}

unsigned long color_of(struct rb_node* node) {
    requires node != 0;
    views node->__rb_parent_color;
    ensures result == (node->__rb_parent_color & 1);
} by {
    execute();
    simp();
}

void set_parent(struct rb_node* node, struct rb_node* parent) {
    requires node != 0;
    requires aligned(parent, 8);
    owns node->__rb_parent_color;
    mutable node->__rb_parent_color;
    ensures node->__rb_parent_color == address(parent) + (old(node->__rb_parent_color) & 1);
} by {
    execute();
    frame();
    simp();
}

void set_black_parent(struct rb_node* node, struct rb_node* parent) {
    requires node != 0;
    requires aligned(parent, 8);
    owns node->__rb_parent_color;
    mutable node->__rb_parent_color;
    ensures node->__rb_parent_color == address(parent) + 1;
} by {
    execute();
    frame();
    simp();
}

struct rb_node* detach_black(struct rb_node* node) {
    requires node != 0;
    owns node->__rb_parent_color;
    mutable node->__rb_parent_color;
    ensures node->__rb_parent_color == 1;
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}

struct rb_node* red_parent_of(struct rb_node* red) {
    requires red != 0;
    requires (red->__rb_parent_color & 1) == 0;
    owns linked(red);
    ensures address(result) == red->__rb_parent_color;
} by {
    unfold(linked(red));
    execute();
    fold(linked(red));
    simp();
}

int32 cleared_is_empty(struct rb_node* node) {
    requires node != 0;
    owns node->__rb_parent_color;
    mutable node->__rb_parent_color;
    ensures result == 1;
} by {
    execute();
    frame();
    simp();
}

int32 relinked_is_empty(struct rb_node* node, struct rb_node* parent) {
    requires node != 0;
    requires aligned(node, 8);
    requires aligned(parent, 8);
    requires parent != node;
    owns node->__rb_parent_color;
    mutable node->__rb_parent_color;
    ensures result == 0;
} by {
    execute();
    frame();
    simp();
}

void link_node(struct rb_node* node, struct rb_node* parent, struct rb_node** rb_link) {
    requires node != 0;
    owns node->__rb_parent_color;
    owns node->rb_left;
    owns node->rb_right;
    owns rb_link[0..1];
    mutable node->__rb_parent_color, node->rb_left, node->rb_right, rb_link[0..1];
    ensures node->__rb_parent_color == address(parent);
    ensures node->rb_left == 0;
    ensures node->rb_right == 0;
    ensures rb_link[0] == node;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
