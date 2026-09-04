# structural recursive calls inside a ranked loop

The loop ranking and the recursive resource ranking are independent: the
finite loop may make a read-only recursive call on the resource's direct child.

```c filename=c_decreases_resource_recursive_in_loop.c
struct node {
    int32 value;
    struct node* next;
};

void zero_walk_loop(struct node* node) {
    int32 i;
    i = 0;
    while (i < 1) {
        if (node->next != 0) {
            zero_walk_loop(node->next);
        }
        i++;
    }
}
```

```click
resource zero_list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        fact node->value == 0;
        contains zero_list(node->next);
    }
}

verifying "c_decreases_resource_recursive_in_loop.c";

void zero_walk_loop(struct node* node) {
    decreases resource zero_list(node);
    requires node != 0;
    views zero_list(node);
    immutable;

} by {
    observe(zero_list(node));
    step();
    step();
    loop {
        decreases 1 - i;
        invariant i >= 0;
        invariant i <= 1;
        immutable by frame;
        initialize by simp;
        preserve by {
            if node->next != 0 {
                step();
                step();
                simp();
            } else {
                step();
                step();
                simp();
            }
            step();
            close_invariants();
        }
    }
    step();
    frame();
}
```

```expect
pass
```
