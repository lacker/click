# a constant view of a billion elements verifies promptly

`views a[0..N]` with a constant `N` makes every element a known cell at entry.
Those cells are one run, recorded once, so reading through the view costs the
same whatever `N` is: a view of a billion elements is as cheap as a view of
eight. Before, every element was stored one by one, a view of a hundred
thousand elements exhausted the simple-tactic budget, and a million collided
two load identities.

The work is pinned independently of `N` by
`surface::tests::scaling_tests::a_constant_view_costs_the_same_whatever_its_length`.
Its negative twin,
[`a_constant_view_of_a_billion_elements_keeps_its_elements_apart.md`](a_constant_view_of_a_billion_elements_keeps_its_elements_apart.md),
checks that the run still keeps two different elements apart.

```c filename=a_constant_view_of_a_billion_elements_verifies_promptly.c
int32 get(int32 *a, int32 i) { return a[i]; }
```

```click
verifying "a_constant_view_of_a_billion_elements_verifies_promptly.c";

int32 get(int32 *a, int32 i) {
    views a[0..1000000000];
    requires 0 <= i;
    requires i < 1000000000;
    ensures result == a[i];
} by {
    execute();
    simp();
}
```

```expect
pass
```
