# A loop that declares only `views` writes nothing

The function owns `p[0..1]`, so the default loop footprint would be that cell.
The loop declares only `views p[0..1]`, so it owns nothing and its footprint is
empty: the body writes only an address-escaped local, and `p[0]` is provably
unchanged after the loop with no invariant naming `p`.

```c filename=loop_views_clause_writes_nothing.c
void loop_views_clause_writes_nothing(int32 p[], int32 n) {
    int32 x;
    int32* px;
    int32 i;
    x = 0;
    px = &x;
    i = 0;
    while (i < n) {
        *px = i;
        i = i + 1;
    }
}
```

```click
verifying "loop_views_clause_writes_nothing.c";

void loop_views_clause_writes_nothing(int32 p[], int32 n) {
    requires n >= 0;
    requires loadable(p[0..1]);
    owns p[0..1];
    ensures p_preserved: p[0] == old(p[0]);
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    loop {
        views p[0..1];
        invariant i >= 0 and i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
