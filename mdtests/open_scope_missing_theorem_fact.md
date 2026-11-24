# An explicit theorem application in an open scope reports its missing premise

```c filename=open_apply.c
void touch(int32* p) { p[0] = 1; }
```

```click
resource cell(p: int32*) { owns p[0..1]; }
theorem needs_zero(value: int32) {
    requires value == 0;
    ensures value == 0 by close();
}
verifying "open_apply.c";
void touch(int32* p) {
    owns cell(p);
    ensures p[0] == 1;
} by {
    with(cell(p)) {
        apply(needs_zero(p[0]));
        step();
    }
}
```

```expect
fail: theorem `needs_zero` has an unproved obligation: `p[0] == 0`
```
