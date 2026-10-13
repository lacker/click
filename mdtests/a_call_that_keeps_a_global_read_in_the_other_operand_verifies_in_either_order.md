# A call that keeps a global read in the other operand verifies in either order

A call and a read of a global in one expression are indeterminately
sequenced. When the call leaves the global's value unchanged, both C orders
give one result, whichever side the call is on, and even when the call
stores the value it read back.

```c filename=keeps_operand.c
int g;
int same(void) { g = g; return 0; }
int one(void) { return 1; }
int call_first(void) { return same() + g; }
int read_first(void) { return g + one(); }
```

```click
verifying "keeps_operand.c";

int same() {
    owns g;
    ensures result == 0 by auto;
    ensures g == old(g) by auto;
}
int one() { ensures result == 1 by auto; }
int call_first() {
    requires g == 5;
    owns g;
    ensures result == 5;
} by { execute(); simp(); }
int read_first() {
    requires g == 5;
    ensures result == 6;
} by { execute(); simp(); }
```

```expect
pass
```
