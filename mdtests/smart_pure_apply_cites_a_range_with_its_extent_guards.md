# Smart pure `apply` cites a range together with its extent guards

A theorem that `views next[0..n]` owes its caller the range and the range's
two extent guards, `0 <= n` and `n <= 1073741823`. A pure theorem that states
the same range has all three facts. Smart `apply` proposes the range
requirement, and the checker accepts it because citing a range cites both of
its halves: the guards join the evidence exactly where they are available.
Search and the checker share that one rule, so the candidate search selects
is the candidate the checker accepts. An explicit `apply using` that names
the range without restating its guards is accepted by the same rule.

```c filename=smart_pure_apply_cites_a_range_with_its_extent_guards.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "smart_pure_apply_cites_a_range_with_its_extent_guards.c";

function walk(next: int32[], from: int32, fuel: Nat) -> int32 decreases fuel {
    match fuel {
        Nat::Zero => from,
        Nat::Succ(previous) => next[walk(next, from, previous)],
    }
}

theorem walk_in_range(next: int32[], n: int32, from: int32, fuel: Nat) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views next[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k] and next[k] < n
    };
    ensures 0 <= walk(next, from, fuel) and walk(next, from, fuel) < n by {
        induct(fuel) as ih {
            Nat::Zero => {
                unfold(walk(next, from, Nat::Zero));
                simp();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                have 0 <= next[walk(next, from, previous)]
                    and next[walk(next, from, previous)] < n by {
                    instantiate(forall (k: int32) {
                        0 <= k and k < n implies 0 <= next[k] and next[k] < n
                    }, walk(next, from, previous)) using {
                        0 <= walk(next, from, previous);
                        walk(next, from, previous) < n;
                    }
                    assumption();
                }
                unfold(walk(next, from, Nat::Succ(previous)));
                assumption();
            }
        }
    }
}

theorem smart_walk_use(a: int32[], n: int32, from: int32, fuel: Nat) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views a[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= a[k] and a[k] < n
    };
    ensures 0 <= walk(a, from, fuel) by {
        apply(walk_in_range(a, n, from, fuel));
    }
}

theorem explicit_walk_use(a: int32[], n: int32, from: int32, fuel: Nat) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views a[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= a[k] and a[k] < n
    };
    ensures 0 <= walk(a, from, fuel) by {
        apply(walk_in_range(a, n, from, fuel)) using {
            0 <= from;
            from < n;
            n <= 1073741823;
            viewable(a[0..n]);
            forall (k: int32) {
                0 <= k and k < n implies 0 <= a[k] and a[k] < n
            };
        }
    }
}

int32 identity(int32 x) {
    ensures result == x by auto;
}
```

```expect
pass
```
