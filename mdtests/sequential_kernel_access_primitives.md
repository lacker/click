# Linux-style access primitives have checked sequential semantics

The source boundary preserves the primitive names while the kernel records
one ordered access for each read or write. Branch prediction wrappers preserve
the condition rather than adding a proof assumption, and pointer publication
remains a sequential store only.

```c filename=sequential_kernel_access_primitives.c
#define __READ_ONCE(x) ({ typeof(x) __value; __value = x; __value; })
#define READ_ONCE(x) __READ_ONCE(x)
#define __WRITE_ONCE(x, value) ({ typeof(x) __value = (value); (*(volatile typeof(x) *)&(x)) = __value; __value; })
#define WRITE_ONCE(x, value) __WRITE_ONCE(x, value)
#define likely(x) __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
#define rcu_assign_pointer(p, v) ({ typeof(p) __value = (v); WRITE_ONCE(p, __value); })

struct node { int32 value; };

int32 sequential_accesses() {
    struct node *link = 0;
    struct node *replacement = 0;
    int32 value = 1;
    value = WRITE_ONCE(value, likely(value) + 1);
    rcu_assign_pointer(link, replacement);
    if (unlikely(value == 2)) return READ_ONCE(value);
    return 0;
}
```

```click
verifying "sequential_kernel_access_primitives.c";

int32 sequential_accesses() {
    ensures result == 2 by auto;
}
```

```expect
pass
```
