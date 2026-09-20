# a global may alias an array argument

`f` reads `a[0]` but declares no resource for `a`, and writes the global `g`
that it owns. Nothing says the caller did not pass `g` as `a`, and `caller`
does exactly that, so carrying `a[0] == 5` across the store to `g[0]` would
let `caller` hold `g[0] == 5` and `g[0] == 1` at one program point.

The two addresses are spelled `arg-memory` and `global:g`, which is a
difference in names and not in objects. The refusal says so, and says what
would settle it — either of the two clauses that do: the `separate(...)` of
`a_separated_array_argument_survives_a_global_store.md`, or the `views a[0..1]`
of `a_views_clause_is_separate_from_an_owns_clause.md`, which is the same
claim made by the contract's own transferred/borrowed split.

```c filename=global_may_alias_an_array_argument.c
int32 g[4];

void f(int32 a[], int32 n) {
    g[0] = 1;
}

void caller() {
    f(g, 4);
}
```

```click
verifying "global_may_alias_an_array_argument.c";

void f(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires a[0] == 5;
    owns g[0..1];
    ensures a[0] == 5;
    ensures g[0] == 1;
} by { execute(); simp(); }

void caller() {
    requires g[0] == 5;
    owns g[0..4];
    ensures g[0] == 5;
} by { execute(); have g[0] == 1 by { simp(); } simp(); }
```

```expect
fail: `a[0]` may have changed since earlier in this function: the store to `g[0]` may have written it, because `a` may point into `g`. If they are separate, require `separate(memory(a[0..1]), memory(g[0..1]))`; where the contract already transfers `g[0..1]` with `owns` or `consumes`, declaring `views a[0..1]` says the same.
```
