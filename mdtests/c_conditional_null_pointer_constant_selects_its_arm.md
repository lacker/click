# The null arm of a pointer conditional is the null pointer

The selected arm decides the value; a claim that ignores the null arm fails.

```c filename=c_conditional_null_pointer_constant_selects_its_arm.c
struct node {
    int value;
};

struct node *drop(struct node *node, int32 pick) {
    return pick ? ((void *)0) : node;
}
```

```click
verifying "c_conditional_null_pointer_constant_selects_its_arm.c";

struct node* drop(struct node* node, int32 pick) {
    requires pick == 1;
    ensures result == node by auto;
}
```

```expect
fail: left side evaluated to 0, right side evaluated to node
```
