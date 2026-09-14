# A fold cannot view memory its own context owns

A body clause `views p[0..1]` names a borrow. When the folding context owns
`p[0..1]` instead, the view is only an observation of that owner, and the
owner can still write the cell after the fold. Capturing `fact p[0] == 0`
inside the composite would then outlive the value it describes: the body
below stores 5 and the claim `result == 0` must not verify. The fold is
refused; the body should own the cell, or receive the view as a borrow.

```click
resource zero(p: int32*) {
    views p[0..1];
    fact p[0] == 0;
}

verifying "fold_cannot_view_memory_its_context_owns.c";

int32 f(int32* p) {
    requires p[0] == 0;
    owns p[0..1];
    ensures result == 0;
} by {
    fold(zero(p));
    step();
    step();
    simp();
}
```

```c filename=fold_cannot_view_memory_its_context_owns.c
int32 f(int32* p) { p[0] = 5; return p[0]; }
```

```expect
fail: body views memory this context owns
```
