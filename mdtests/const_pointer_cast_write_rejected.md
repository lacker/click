# Qualified pointer casts reject writes through const views

Both a direct const-qualified cast and a pointer variable initialized from that
cast remain read-only lvalues.

```c filename=const_pointer_cast_write.c
struct node {
    int32 value;
};

void direct(const struct node *node) {
    node->value = 3;
}

void indirect(struct node *node) {
    const struct node *view = (const struct node *)node;
    view->value = 3;
}
```

```click
verifying "const_pointer_cast_write.c";
```

```expect
fail:const-qualified
```
