# rbtree parent-color helpers preserve packed parent addresses

The `rb_node` word packs a parent pointer and one color bit. The header
carries the Linux helper shapes unchanged. These contracts compare the
recovered numeric addresses; they grant no dereference authority for them.
The relinked-node check requires distinct parent and node addresses because
C compares the packed word numerically. Pointer-value disequality alone can
also distinguish different provenances at one address. Its proof masks the
word and uses alignment to rule out the empty-node marker. The link helper
proves that each store preserves the fields initialized by earlier stores.

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
theorem equal_words_keep_mask(left: uint64, right: uint64, mask: uint64) {
    requires left == right;
    ensures (left & mask) == (right & mask) by {
        rewrite(left, right);
        close();
    }
}

resource linked(node: struct rb_node*) {
    owns node->__rb_parent_color;
    fact aligned(node, 8);
    let parent: struct rb_node* where aligned(parent, 8) and
        node->__rb_parent_color == address(parent) + (node->__rb_parent_color & 1);
}

verifying "rb_parent_family.c";

void rb_link_node(struct rb_node* node, struct rb_node* parent, struct rb_node** rb_link) {
    requires node != 0;
    owns node->__rb_parent_color;
    owns node->rb_left;
    owns node->rb_right;
    owns rb_link[0..1];
    ensures node->__rb_parent_color == address(parent);
    ensures node->rb_left == 0;
    ensures node->rb_right == 0;
    ensures rb_link[0] == node;
} by {
    step();
    step();
    have separate(memory(node->rb_left), memory(node->__rb_parent_color)) by { close(); }
    have separate(statement(1).footprint, memory(node->__rb_parent_color)) by {
        normalize() using { separate(memory(node->rb_left), memory(node->__rb_parent_color)); };
    }
    have node->__rb_parent_color == at(statement(1).entry, node->__rb_parent_color) by {
        preserve(memory(node->__rb_parent_color), statement(1));
    }
    step();
    have separate(memory(node->rb_right), memory(node->__rb_parent_color)) by { close(); }
    have separate(statement(2).footprint, memory(node->__rb_parent_color)) by {
        normalize() using { separate(memory(node->rb_right), memory(node->__rb_parent_color)); };
    }
    have node->__rb_parent_color == at(statement(2).entry, node->__rb_parent_color) by {
        preserve(memory(node->__rb_parent_color), statement(2));
    }
    have separate(memory(node->rb_right), memory(node->rb_left)) by { close(); }
    have separate(statement(2).footprint, memory(node->rb_left)) by {
        normalize() using { separate(memory(node->rb_right), memory(node->rb_left)); };
    }
    have node->rb_left == at(statement(2).entry, node->rb_left) by {
        preserve(memory(node->rb_left), statement(2));
    }
    step();
    have separate(memory(rb_link[0]), memory(node->__rb_parent_color)) by { close(); }
    have separate(statement(3).footprint, memory(node->__rb_parent_color)) by {
        normalize() using { separate(memory(rb_link[0]), memory(node->__rb_parent_color)); };
    }
    have node->__rb_parent_color == at(statement(3).entry, node->__rb_parent_color) by {
        preserve(memory(node->__rb_parent_color), statement(3));
    }
    have separate(memory(rb_link[0]), memory(node->rb_left)) by { close(); }
    have separate(statement(3).footprint, memory(node->rb_left)) by {
        normalize() using { separate(memory(rb_link[0]), memory(node->rb_left)); };
    }
    have node->rb_left == at(statement(3).entry, node->rb_left) by {
        preserve(memory(node->rb_left), statement(3));
    }
    have separate(memory(rb_link[0]), memory(node->rb_right)) by { close(); }
    have separate(statement(3).footprint, memory(node->rb_right)) by {
        normalize() using { separate(memory(rb_link[0]), memory(node->rb_right)); };
    }
    have node->rb_right == at(statement(3).entry, node->rb_right) by {
        preserve(memory(node->rb_right), statement(3));
    }
    step();
    close();
}

struct rb_node* parent_of(struct rb_node* node) {
    requires node != 0;
    owns linked(node);
    ensures address(result) == (node->__rb_parent_color & ~3);
} by {
    unfold(linked(node));
    step_until(function.exit);
    have address(result) == (node->__rb_parent_color & ~3) by {
        close() using {
            aligned(result, 8);
            node->__rb_parent_color == address(result) + (node->__rb_parent_color & 1);
        };
    }
    fold(linked(node));
    close();
}

unsigned long color_of(struct rb_node* node) {
    requires node != 0;
    views node->__rb_parent_color;
    ensures result == (node->__rb_parent_color & 1);
}

void set_parent(struct rb_node* node, struct rb_node* parent) {
    requires node != 0;
    requires aligned(parent, 8);
    owns node->__rb_parent_color;
    ensures node->__rb_parent_color == address(parent) + (old(node->__rb_parent_color) & 1);
}

void set_black_parent(struct rb_node* node, struct rb_node* parent) {
    requires node != 0;
    requires aligned(parent, 8);
    owns node->__rb_parent_color;
    ensures node->__rb_parent_color == address(parent) + 1;
}

struct rb_node* detach_black(struct rb_node* node) {
    requires node != 0;
    owns node->__rb_parent_color;
    ensures node->__rb_parent_color == 1;
    ensures result == 0;
}

struct rb_node* red_parent_of(struct rb_node* red) {
    requires red != 0;
    requires (red->__rb_parent_color & 1) == 0;
    owns linked(red);
    ensures address(result) == red->__rb_parent_color;
} by {
    unfold(linked(red));
    step_until(function.exit);
    have address(result) == red->__rb_parent_color by {
        close() using {
            (red->__rb_parent_color & 1) == 0;
            red->__rb_parent_color == address(result) + (red->__rb_parent_color & 1);
        };
    }
    fold(linked(red));
    close();
}

int32 cleared_is_empty(struct rb_node* node) {
    requires node != 0;
    owns node->__rb_parent_color;
    ensures result == 1;
}

int32 relinked_is_empty(struct rb_node* node, struct rb_node* parent) {
    requires node != 0;
    requires aligned(node, 8);
    requires aligned(parent, 8);
    requires address(parent) != address(node);
    owns node->__rb_parent_color;
    ensures result == 0;
} by {
    step();
    have address(parent) == (node->__rb_parent_color & ~3) by close() using {
        aligned(parent, 8);
    };
    have address(node) == (address(node) & ~3) by close() using {
        aligned(node, 8);
    };
    have node->__rb_parent_color != address(node) by {
        if node->__rb_parent_color == address(node) {
            apply(equal_words_keep_mask(node->__rb_parent_color, address(node), ~3u64));
            have address(parent) == address(node) by {
                close();
            }
            contradiction(address(parent) == address(node));
        } else {
            close();
        }
    }
}

void link_node(struct rb_node* node, struct rb_node* parent, struct rb_node** rb_link) {
    requires node != 0;
    owns node->__rb_parent_color;
    owns node->rb_left;
    owns node->rb_right;
    owns rb_link[0..1];
    ensures node->__rb_parent_color == address(parent);
    ensures node->rb_left == 0;
    ensures node->rb_right == 0;
    ensures rb_link[0] == node;
}
```

```expect
pass
```
