# A post-call equality does not survive a later store

The call establishes g == 11, but the subsequent store changes g to 1001.
The old equality cannot justify a bound on the new read.

```c filename=global.c
int g;
int bumpg(void) { g = g + 1; return 0; }
int h(void) { int a = bumpg(); g = 1001; return a; }
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
    step(); step(); step();
    have g < 1000;
    execute(); simp();
}
```

```expect
fail: could not establish `g < 1000`
```
