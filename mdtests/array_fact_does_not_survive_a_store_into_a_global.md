# epoch attack 5: a store into a global the argument may be

`arg-memory` and `global:g` are two fully known block names that differ, and
that is not a reason to cross the store. `global_may_alias_an_array_argument.md`
is the caller that passes `g` as `a`, so an epoch that crossed here would carry
`icount(a, 0, 1) == 5` past the write that makes `a[0]` one, and the caller
would hold two values for `g[0]` at one point.

The fact carries content -- `icount(a, 0, 1) == 5` comes from
`requires a[0] == 5` through the fold's defining equation -- so the refusal is
not an artifact of a fold over an empty range.

Two edges stop the walk here, and both have to. A store statement first forgets
every cell it might overwrite -- here `g[0]`'s own, which a zero-initialized
global always has -- and that `CellsForgotten` edge is one the walk never
crosses. Under it is the `Store` edge into a block that is not proven distinct
from the argument's, which stops the walk on its own; the kernel test
`an_array_refs_epoch_stops_at_a_store_that_may_alias_it` is what pins that
second edge, since no C store reaches it without the first.

```c filename=array_fact_does_not_survive_a_store_into_a_global.c
int32 g[4];

void f(int32 a[], int32 n) {
    g[0] = 1;
}
```

```click
verifying "array_fact_does_not_survive_a_store_into_a_global.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void f(int32 a[], int32 n) {
    requires 0 < n;
    requires loadable(a[0..n]);
    requires a[0] == 5;
    owns g[0..1];
    views a[0..n];
} by {
    have 0 <= 0 by { simp(); }
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    have to_integer(a[0]) == 5 by { simp() using { a[0] == 5; }; }
    have icount(a, 0, 1) == 5 by {
        unfold(icount(a, 0, 1)) using { 0 <= 0; 0 < 2147483647; }
        arithmetic() using { icount(a, 0, 0) == 0; to_integer(a[0]) == 5; }
    }
    step();
    have icount(a, 0, 1) == 5 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: tactic 5: `have` failed for `icount(a, 0, 1) == 5`
```
