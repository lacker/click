# a pointer a call returned may alias the global it points at

`pick` returns `&g[0]`, so in `f` the pointer `a` *is* `&g[0]` and the store
`g[0] = 1` changes what `a[0]` reads. Carrying `a[0] == 5` across that store
would let `f` hold `a[0] == 5` and `g[0] == 1` at one program point, with
`a == &g[0]` in the context as well: three facts that cannot all be true.

The two addresses are spelled `symbolic-pointer:...` and `global:g`. A pointer
value the verifier does not resolve is separated from nothing at all, so that
difference is a difference in names and not in objects, exactly as
`arg-memory` beside `global:g` is in `global_may_alias_an_array_argument.md`.
The refusal says so and names the store it has to be told apart from. It
cannot offer a `separate(..)` here: the read has no source spelling of its own,
because it goes through a pointer the function received rather than an object
it names.

```c filename=returned_pointer_may_alias_a_global.c
int32 g[4];

int32* pick(void) { return &g[0]; }

void f(void) {
    int32* a;
    a = pick();
    g[0] = 1;
}
```

```click
verifying "returned_pointer_may_alias_a_global.c";

int32* pick() {
    views g[0..1];
    requires g[0] == 5;
    ensures viewable(result[0..1]);
    ensures result[0] == 5;
    ensures result == &g[0];
} by { execute(); simp(); }

void f() {
    owns g[0..4];
    requires g[0] == 5;
    ensures g[0] == 1;
} by {
    step();
    step();
    step();
    have a[0] == 5 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: the store to `g[0]` may have written it, and nothing tells that address apart from this read.
```
