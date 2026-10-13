# A call that changes a global read in the other operand is refused

C evaluates `bump()` and the read of `g` in `bump() + g` in either order,
so the sum is 1 or 2. Click reads `g` on both sides of the call and requires
one value; `bump` changes it, so the expression is refused instead of
verified under one chosen order.

```c filename=changes_operand.c
int g;
int bump(void) { g = g + 1; return 0; }
int f(void) { return bump() + g; }
```

```click
verifying "changes_operand.c";

int bump() {
    requires g < 100;
    owns g;
    ensures result == 0 by auto;
    ensures g == old(g) + 1 by auto;
}
int f() {
    requires g == 0;
    owns g;
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
fail: the call leaves `g`, read in the other operand, unchanged
```
