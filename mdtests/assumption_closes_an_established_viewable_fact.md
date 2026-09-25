# `assumption()` closes a `viewable` goal from the identical established fact

A narrowing established by `transport … using` is an ordinary available fact,
and `assumption()` closes the identical `viewable` goal from it through the
same exact indexed lookup it uses for any other goal. The DFS proofs once
reported

```text
`assumption` requires the current goal as an available semantic fact: current
goal is a memory-viewability fact
```

which left no way to finish a `both { ... }` arm whose goal was a narrowed
range. Here the narrowing is established once, then cited: from a `both` arm,
and under a universal after `intro`.

The rule is exact, not a narrowing: a different range or a different snapshot
does not close the goal
(`mdtests/assumption_does_not_close_a_viewable_goal_at_another_range.md`,
`mdtests/assumption_does_not_close_a_viewable_goal_at_another_snapshot.md`).

```c filename=assumption_closes_an_established_viewable_fact.c
int32 probe(int32 a[], int32 n, int32 k) {
    return 0;
}
```

```click
verifying "assumption_closes_an_established_viewable_fact.c";

int32 probe(int32 a[], int32 n, int32 k) {
    requires 0 <= k;
    requires k <= n;
    requires n <= 1073741823;
    views a[0..n];
    ensures result == 0;
} by {
    step();
    have viewable(a[0..n]) by { simp(); }
    have viewable(a[0..k]) by {
        transport(viewable(a[0..n]), viewable(a[0..k])) using {
            viewable(a[0..n]);
            0 <= k;
            k <= n;
            0 <= n - 0;
            n - 0 <= 1073741823;
        }
    }
    have viewable(a[0..k]) and 0 <= k by {
        both { assumption(); } and { simp(); }
    }
    have forall (j: int32) { 0 <= j and j <= k implies viewable(a[0..j]) } by {
        intro();
        intro();
        extract(0 <= j);
        extract(j <= k);
        have j <= n by { arithmetic() using { j <= k; k <= n; } }
        have viewable(a[0..j]) by {
            transport(viewable(a[0..n]), viewable(a[0..j])) using {
                viewable(a[0..n]);
                0 <= j;
                j <= n;
                0 <= n - 0;
                n - 0 <= 1073741823;
            }
        }
        assumption();
    }
    simp();
}
```

```expect
pass
```
