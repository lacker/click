# an owner is not separate from its own observation view

The entry partition pairs a contract's transferred clauses with its
*borrowed* ones, and the discriminator is the clause list, not the context.
`owns g[0..1]` also publishes `views g[0..1]` into the body's context — an
owner observation of the very range it describes
(`MemoryResourceAlgebra::pair_validity_error`,
`ResourceContext::observable_facts_assuming_valid`). Pairing an owner with
that view would separate a range from itself.

This contract has a real (borrowed, transferred) pair, so the entry facts are
built; the false claim below asks whether `g`'s own store was framed away from
`g`. It is not: the store is seen, and `g[0] == 5` no longer holds.

```c filename=an_owner_is_not_separate_from_its_own_observation.c
int32 g[4];

void f(int32 a[], int32 n) {
    g[0] = 1;
}
```

```click
verifying "an_owner_is_not_separate_from_its_own_observation.c";

void f(int32 a[], int32 n) {
    requires 0 < n;
    requires a[0] == 5;
    requires g[0] == 5;
    views a[0..n];
    owns g[0..1];
    ensures g[0] == 5;
} by { execute(); simp(); }
```

```expect
fail: `ensures g[0] == 5` failed for `f.ensures_1` path 0: unclosed goal: g[0] == 5; left side evaluated to 1, right side evaluated to 5
```
