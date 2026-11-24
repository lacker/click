# a structural resource measure refuses a cross-member call that does not descend

`odd` passes its own `node` to `even`. That is the instance `odd` measures,
not a contained child of it, so the call is refused by name.

```c filename=c_decreases_resource_mutual_recursion_must_descend_even.c
struct node { int value; struct node *next; };

int even(struct node *node) {
    int result;
    if (node != 0) {
        result = odd(node->next);
        return result;
    }
    return 0;
}
```

```c filename=c_decreases_resource_mutual_recursion_must_descend_odd.c
struct node { int value; struct node *next; };

int odd(struct node *node) {
    int result;
    if (node != 0) {
        result = even(node);
        return result;
    }
    return 0;
}
```

```click
resource list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->next;
        owns list(node->next);
    }
}

verifying "c_decreases_resource_mutual_recursion_must_descend_even.c";
verifying "c_decreases_resource_mutual_recursion_must_descend_odd.c";

int32 even(struct node* node) {
    decreases list(node);
    views list(node);
    ensures result == 0;
} by {
    if node == 0 {
        step_until(function.exit);
        close();
    } else {
        observe(list(node));
        step_until(function.exit);
        close();
    }
}

int32 odd(struct node* node) {
    decreases list(node);
    views list(node);
    ensures result == 0;
} by {
    if node == 0 {
        step_until(function.exit);
        close();
    } else {
        observe(list(node));
        step_until(function.exit);
        close();
    }
}
```

```expect
fail: must receive a retained child witness of the entry resource
```
