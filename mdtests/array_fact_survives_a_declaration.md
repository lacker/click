# a fact about an array survives a declaration

`int32 t;` brings a new object into the memory model and writes nothing. It
has its own name, so the extent, contents, overlays, liveness and heap status
of `a` are all the ones they were, and a fact about `a` as a whole is still
the fact — exactly as `a[0] == 5` has always survived this step.

```c filename=array_fact_survives_a_declaration.c
void bump(int32 a[], int32 n) {
    int32 t;
    t = 0;
}
```

```click
verifying "array_fact_survives_a_declaration.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void bump(int32 a[], int32 n) {
    requires 0 < n;
    requires a[0] == 5;
    views a[0..n];
} by {
    have 0 <= 0 by { simp(); }
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    step();
    have icount(a, 0, 0) == 0 by { simp(); }
    execute();
    simp();
}
```

```expect
pass
```
