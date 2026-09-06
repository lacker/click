# structural descent through a resource witness child

A `let` witness of a recursive resource has no C spelling, so a recursive
call cannot name it syntactically. The structural measure accepts the call
when the exact definition, instantiated over a symbolic entry state, lets the
pure kernel decide that the call's argument is the witness pointer: here the
where-fact and the alignment evidence make `(struct node *)(node->word & ~1)`
the witness. The ordinary contract still certifies the resource transfer.

```c filename=c_decreases_resource_witness_child.c
struct node {
    int32 value;
    unsigned long word;
};

uint32 count_nodes(struct node *node) {
    if (node == 0) {
        return 0;
    }
    uint32 rest = count_nodes((struct node *)(node->word & ~1));
    return rest + 1;
}
```

```click
resource marked_list(node: struct node*) {
    if node != 0 {
        contains allocation(node, sizeof(struct node));
        owns object(node);
        fact aligned(node, 8);
        let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
        contains marked_list(next);
    }
}

verifying "c_decreases_resource_witness_child.c";

uint32 count_nodes(struct node* node) {
    decreases resource marked_list(node);
    owns marked_list(node);
} by {
    if node == 0 {
        execute();
        simp();
    } else {
        unfold(marked_list(node));
        execute();
        fold(marked_list(node));
        simp();
    }
}
```

```expect
pass
```
