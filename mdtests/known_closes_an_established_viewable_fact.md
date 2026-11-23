# `known()` closes a `viewable` goal from the identical established fact

A narrowing established by the separation restriction axioms is an ordinary available fact,
and `known()` closes the identical `viewable` goal from it through the
same exact indexed lookup it uses for any other goal. The DFS proofs once
failed to close a `both` arm with this narrowed range even after proving it.
This fixture cites the narrowing from a `both` arm and under a universal
after `intro`.

The rule is exact, not a narrowing: a different range or a different state
does not close the goal
(`mdtests/known_does_not_close_a_viewable_goal_at_another_range.md`,
`mdtests/known_does_not_close_a_viewable_goal_at_another_state.md`).

```c filename=known_closes_an_established_viewable_fact.c
int32 probe(int32 a[], int32 n, int32 k) {
    return 0;
}
```

```click
verifying "known_closes_an_established_viewable_fact.c";

int32 probe(int32 a[], int32 n, int32 k) {
    requires 0 <= k;
    requires k <= n;
    requires n <= 1073741823;
    views a[0..n];
    ensures result == 0;
} by {
    step();
    have viewable(a[0..n]);
    have 0 <= n - 0;
    have n - 0 <= 1073741823;
    have 0 <= 0 by { known(); }
    have viewable(a[0..k]) by {
        have contains(memory(a[0..n]), memory(a[0..k])) by {
            apply(click::separation::contains_subrange(a, 0, n, 0, k));
        }
        apply(click::separation::viewable_restrict(memory(a[0..n]), memory(a[0..k])));
    }
    have viewable(a[0..k]) and 0 <= k by {
        all { viewable(a[0..k]) => { known(); } 0 <= k => { solve(); } }
    }
    have forall (j: int32) { 0 <= j and j <= k implies viewable(a[0..j]) } by {
        intro(); intro();
        have j <= n by { solve() using { j <= k; k <= n; }; }
        have viewable(a[0..j]) by {
            have contains(memory(a[0..n]), memory(a[0..j])) by {
                apply(click::separation::contains_subrange(a, 0, n, 0, j));
            }
            apply(click::separation::viewable_restrict(memory(a[0..n]), memory(a[0..j])));
        }
        known();
    }
    solve();
}
```

```expect
pass
```
