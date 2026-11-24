# A C-valued contract `let` in Integer arithmetic

Under Integer specification arithmetic a comparison that does arithmetic compares exact
Integers, observing each machine operand with `to_integer`. A contract `let`
that names a C value is such an operand: `entry + 1` below is
`to_integer(old(b->cap)) + 1`, as it would be written with `old(b->cap)` in
place of `entry`. The function shape is the owned-vector example's
`vector_grow`.

```c filename=let_entry.c
struct box { int cap; };
void grow(struct box *b) {
    b->cap = b->cap + 1;
}
```

```click
verifying "let_entry.c";

void grow(struct box* b) {
    let entry = old(b->cap);
    requires 0 <= b->cap and b->cap <= 1000;
    owns *b;
    ensures b->cap == entry + 1;
} by {
    step();
    step();
    close();
}
```

```expect
pass
```
