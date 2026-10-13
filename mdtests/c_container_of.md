# Linux container_of checks its types and preserves the enclosing address

The macro body is retained from Linux v6.8.12's `include/linux/container_of.h`
(GPL-2.0-or-later), as pinned by the Linux rbtree integration archive.
This checks the complete expression for a first member; metadata ownership
and nonzero enclosing-object recovery are separate proof obligations.

```c filename=container.c
struct rb_node { int32 value; };
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

struct sized_node* enclosing(struct rb_node* rb) {
    return container_of(rb, struct sized_node, rb);
}
```

```click
verifying "container.c";
struct sized_node* enclosing(struct rb_node* rb) {
    ensures address(result) == address(rb);
} by { execute(); normalize(); }
```

```expect
pass
```
