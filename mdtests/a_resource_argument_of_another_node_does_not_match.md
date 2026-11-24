# A resource argument of another node does not match

`caller` holds `size_metadata(rb_other)` and calls `set_size` for the node
enclosing `rb_old`. Resource argument identity ignores the view a cast
selects, but it still compares address and provenance: `rb_other` is a
different pointer, so the held instance does not supply the callee's
`size_metadata(node as (uint8 *) as (struct rb_node *))`. The positive form, with the
same node through another view, is
[`a_resource_argument_matches_across_a_cast_that_selects_another_view.md`](a_resource_argument_matches_across_a_cast_that_selects_another_view.md).

```c filename=a_resource_argument_of_another_node_does_not_match.c
struct rb_node { struct rb_node *rb_right; struct rb_node *rb_left; };
struct sized_node { struct rb_node rb; int size; };
#define offsetof(TYPE, MEMBER) __builtin_offsetof(TYPE, MEMBER)
#define container_of(ptr, type, member) ({				\
	void *__mptr = (void *)(ptr);					\
	((type *)(__mptr - offsetof(type, member))); })

int set_size(struct sized_node *node) {
    node->size = 1;
    return 0;
}

void caller(struct rb_node *rb_old, struct rb_node *rb_other) {
    struct sized_node *old = container_of(rb_old, struct sized_node, rb);
    set_size(old);
}
```

```click
verifying "a_resource_argument_of_another_node_does_not_match.c";

resource size_metadata(node: struct rb_node*) {
    field value: int32;
    owns (node as (uint8 *) as (struct sized_node *))->size;
    fact (node as (uint8 *) as (struct sized_node *))->size == value;
}

int32 set_size(struct sized_node* node) {
    requires defined(&node->size);
    owns parent: size_metadata(node as (uint8 *) as (struct rb_node *));
    ensures parent.value == 1;
} by {
    unfold(parent);
    step_until(function.exit);
    let parent = fold(size_metadata(node as (uint8 *) as (struct rb_node *)), { value: 1 });
    close();
}

void caller(struct rb_node* rb_old, struct rb_node* rb_other) {
    owns source: size_metadata(rb_other);
    ensures source.value == 1;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    step(set_size, { parent: source });
}
```

```expect
fail: equality of resource argument 1 was not established
```
