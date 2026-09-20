# a pointer equality resolves a read through a returned pointer

The sibling of `returned_pointer_may_alias_a_global.md`, on the same C. There
`a[0] == 5` is refused after `g[0] = 1`, because it is false. Here the *true*
statement about the same read is proved: `a` is `&g[0]`, the store wrote `1`,
so `a[0]` is `1`.

Since `a`'s block is a pointer value the verifier does not resolve, nothing
structural relates it to `g`. The evidence is the stated equality, and the
proof names it once with a `have` before the read; that is the universal
fallback, and it is also what puts the equality in the context at the
frontier the read is made from. One hop through that exact equality is then
enough: the read is asked again at the address the program names, where the
store to `g[0]` is the store it reads.

```c filename=returned_pointer_resolved_by_a_pointer_equality.c
int32 g[4];

int32* pick(void) { return &g[0]; }

void f(void) {
    int32* a;
    a = pick();
    g[0] = 1;
}
```

```click
verifying "returned_pointer_resolved_by_a_pointer_equality.c";

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
    have a == &g[0] by { simp(); }
    have a[0] == 1 by { simp(); }
    execute();
    simp();
}
```

```expect
pass
```
