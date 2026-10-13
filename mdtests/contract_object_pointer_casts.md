# Contract object pointers retain explicit layouts through void

The copy body is the generated Linux augmentation callback. The container_of
macro body is retained from Linux v6.8.12 (GPL-2.0-or-later).

```c filename=copy.c
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};
struct sized_node { struct rb_node rb; int32 size; };
#define offsetof(TYPE, MEMBER) __builtin_offsetof(TYPE, MEMBER)
#define __same_type(a, b) __builtin_types_compatible_p(typeof(a), typeof(b))
#define static_assert _Static_assert
#define rb_entry(ptr, type, member) container_of(ptr, type, member)
#define container_of(ptr, type, member) ({				\
	void *__mptr = (void *)(ptr);					\
	static_assert(__same_type(*(ptr), ((type *)0)->member) ||	\
		      __same_type(*(ptr), void),			\
		      "pointer type mismatch in container_of()");	\
	((type *)(__mptr - offsetof(type, member))); })

static inline void sized_copy(struct rb_node *rb_old, struct rb_node *rb_new)
{
    struct sized_node *old = rb_entry(rb_old, struct sized_node, rb);
    struct sized_node *new = rb_entry(rb_new, struct sized_node, rb);
    new->size = old->size;
}

struct sized_node* identity(struct rb_node* p) {
    return (struct sized_node*)(void*)p;
}
```

```click
verifying "copy.c";
void sized_copy(struct rb_node* rb_old, struct rb_node* rb_new) {
    views ((struct sized_node*)(void*)rb_old)->size;
    owns ((struct sized_node*)(void*)rb_new)->size;
    ensures ((struct sized_node*)(void*)rb_new)->size == old(((struct sized_node*)(void*)rb_old)->size);
    ensures ((struct sized_node*)(void*)rb_old)->size == old(((struct sized_node*)(void*)rb_old)->size);
} by { execute(); simp(); }
struct sized_node* identity(struct rb_node* p) {
    ensures address(result) == address((struct sized_node*)(void*)p);
} by { execute(); simp(); }
```

```expect
pass
```
