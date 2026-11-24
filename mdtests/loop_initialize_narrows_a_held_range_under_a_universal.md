# A quantified viewable invariant is initialized by narrowing the held range

The loop states that every prefix of the viewed range is viewable:
`forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) }`. Its
`initialize` proof is the same one a function body writes for the same fact:
introduce `k` and its antecedent, extract the two bounds, and let `close()`
narrow the held `views a[0..n]`.

The local `steps` is declared before the loop, so the loop-entry memory is a
later state than function entry. The function body relates the two when it
spells the contract's range for a narrowing step; the `initialize` phase is a
fixed-state proof at the loop entry, and its planner used to see no fixed-state
view there at all. `close()` then had no spelling for the entry-state range and
refused to narrow it, although an explicit `transport` of the same fact checked.
A fixed-state proof now offers its own state to that planner.

The back edge owes the invariant's span bound for every `k`, the `uint32`
order `k <=u 1073741823`. The back edge closes that member the way it closes
an unquantified one: it introduces `k` and the antecedent `0 <= k and k <= n`,
and decides the bound from those two conjuncts and `n <= 1073741823` by signed
order. It used to stop at the quantifier, so the preservation proof had to
state the unsigned bound itself.

```c filename=loop_initialize_narrows_a_held_range_under_a_universal.c
int32 count_up(int32 *a, int32 n) {
    int32 steps = 0;
    for (int32 i = 0; i < n; i++) {
        steps = i;
    }
    return steps;
}
```

```click
verifying "loop_initialize_narrows_a_held_range_under_a_universal.c";

int32 count_up(int32 *a, int32 n) {
    views a[0..n];
    requires 0 <= n;
    requires n <= 1073741823;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) };
        initialize by {
            have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {
                intro();
                intro();
                have 0 <= k;
                have k <= n;
                close();
            }
            close();
        }
        maintain by {
            step();
            step();
            have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {
                intro();
                intro();
                have 0 <= k;
                have k <= n;
                close();
            }
        }
    }
}
```

```expect
pass
```
