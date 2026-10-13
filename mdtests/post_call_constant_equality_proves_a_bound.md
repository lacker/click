# A retained post-call equality proves a bound directly

The call establishes g == 11. A bound on that same read needs no intermediate
have that restates the equality.

```c filename=global.c
int g;
int bumpg(void) { g = g + 1; return 0; }
int h(void) { int a = bumpg(); return a; }
```

```click
verifying "global.c";
int bumpg() {
    requires g < 1000;
    owns g;
    ensures result == 0 by auto;
    ensures g == old(g) + 1 by auto;
}
int h() {
    requires g == 10;
    owns g;
    ensures result == 0;
} by {
    step(); step();
    have g > -1000;
    execute(); simp();
}
```

```expect
pass
```
