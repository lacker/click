# A named interface resource keeps only what the interface states about its model

The interface names the cell but says nothing about its model. The join gives
`c` a fresh model, so the postcondition relating it to the entry model is no
longer provable, and the refusal says where the model was replaced.

```c filename=ife4.c
struct cell { int32 value; };

int32 peek(struct cell *node, int32 x) {
    int32 a;
    a = 0;
    return a;
}
```

```click
verifying "ife4.c";

resource cell(p: struct cell*) {
    field model: int32;
    owns p->value;
    fact p->value == model;
}

int32 peek(struct cell* node, int32 x) {
    requires node != 0;
    owns c: cell(node);
    ensures result == 0;
    ensures c.model == old(c.model);
} by {
    step();
    if x <= 0 ensuring {
        owns c: cell(node);
    } then {
        unfold(c);
        let c = fold(cell(node), { model: node->value });
    } else {
    }
    step();
    step();
    close();
}
```

```expect
fail: the join gives `c` a fresh one
```
