# a structural measure keeps checking past a switch

`4ab4c50a` fixed the `switch` shape in `recursion_paths`, the `decreases
<int32 parameter>` walk, and recorded that `structural_recursion_paths` — the
resource-measure walk beside it — had the same shape and the opposite `break`,
untouched because no witness had been built for it. This is that witness.

The resource walk carries one path per way of reaching a statement and checks
each recursive call once per path, so an empty path list is a recursive call
nothing checks. A `switch` answered the union of its *case bodies'* answers
and nothing else, dropping the selector path that matches no case and runs no
case body at all. One case, ending in a `return`, and no `default`, empties
the list; `Seq` keeps it empty and the later `if` iterates over it, so every
recursive call after the switch went unwalked:

    int32 spin_past_a_switch(struct node* node, int32 k) {
        int32 result;
        result = 0;
        switch (k) {
            case 0:
                return 0;
        }
        result = spin_past_a_switch(node, k);
        return result;
    }

`spin_past_a_switch(p, 1)` calls `spin_past_a_switch(p, 1)`, and `decreases
zero_list(node)` verified. Termination is the only C judgment, so that is a
false theorem. The same body with the `switch` replaced by `if (k == 0) {
return 0; }` was already refused, which is what said the switch was the
trigger. So were the same switch with a `break` in its case, and the same
switch with a `default` — either keeps one path alive and the guard fires.

The two walks now share one control-flow skeleton, `walk_termination_paths`,
so a `switch`, a `break`, a `return`, and an unentered branch arm mean the
same thing to both measure forms and a third form cannot re-derive the
mistake. Each walk keeps its own paths and its own checks.

`zero_walk_past_a_switch` is the positive next door: the same switch in front
of `c_decreases_resource_recursive`'s descending walk, which still verifies.

```c filename=c_decreases_resource_checks_past_a_switch.c
struct node {
    int32 value;
    struct node* next;
};

int32 zero_walk_past_a_switch(struct node* node, int32 k) {
    struct node* next;
    int32 result;
    switch (k) {
        case 0:
            return 0;
    }
    next = node->next;
    if (next == 0) {
        return node->value;
    }
    result = zero_walk_past_a_switch(next, k);
    return result;
}

int32 spin_past_a_switch(struct node* node, int32 k) {
    int32 result;
    result = 0;
    switch (k) {
        case 0:
            return 0;
    }
    result = spin_past_a_switch(node, k);
    return result;
}
```

```click
resource zero_list(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns &node->next;
        fact node->value == 0;
        contains zero_list(node->next);
    }
}

verifying "c_decreases_resource_checks_past_a_switch.c";

int32 zero_walk_past_a_switch(struct node* node, int32 k) {
    decreases zero_list(node);
    requires node != 0;
    views zero_list(node);

    ensures result == 0;
} by {
    observe(zero_list(node));
    execute();
    simp();
}

int32 spin_past_a_switch(struct node* node, int32 k) {
    decreases zero_list(node);
    requires node != 0;
    views zero_list(node);

    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: does not pass a direct contained child of its structural resource measure
```
