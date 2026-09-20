# a contract's `views` clause is separate from its own `owns` clause

The companion of `a_separated_array_argument_survives_a_global_store.md`,
which states the same separation by hand. Here nothing is stated: `a` is
lent by a `views` clause and `g` is transferred by an `owns` clause of the
same contract, and the entry partition says those denote disjoint memory
(`docs/internals/resource-tracker.md`, "The entry partition"). The read of
`a[0]` is framed across the store to `g[0]`, with no `separate(...)` clause
and no `viewable(...)` requirement.

```c filename=a_views_clause_is_separate_from_an_owns_clause.c
int32 g[4];

void f(int32 a[], int32 n) {
    g[0] = 1;
}
```

```click
verifying "a_views_clause_is_separate_from_an_owns_clause.c";

void f(int32 a[], int32 n) {
    requires 0 < n;
    requires a[0] == 5;
    views a[0..n];
    owns g[0..1];
    ensures a[0] == 5;
    ensures g[0] == 1;
} by { execute(); simp(); }
```

```expect
pass
```
