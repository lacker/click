# a counting invariant survives the store that changes the count

`sweep` marks every cell of `visited[0..n]`. Its termination is the ordinary
`decreases n - i`; the counting content is the invariant
`unmarked(visited, 0, i) == 0`, that everything below the cursor is marked.

Two steps of the body need memory reasoning the proof does not spell out.
Appending the written cell reads it out of the snapshot the store produced, so
the append law's last cell is the value that store wrote. Carrying the
invariant past the cursor's own `i++` needs the array argument `unmarked`
folds over to name the same snapshot on both sides of a step that writes only
a local, which is what a block epoch gives it.

`unmarked_frame` is the part that is still written out: it carries the entry
invariant across the write, for the cells below the cursor, through one
`transport ... using` per cell under two `intro()`s. It is a verbatim copy of
`mdtests/unmarked_count_lemmas.md`, because an `import` shares a theorem's
statement and assumes its proof, and no gate selects a `mdtests/*.click`
library as an entry.

The body's bookkeeping is what a `using` list can cite without a `have` first:
the invariants, the loop guard, and a stated range's extent halves are all
available by name, so twenty-six of the thirty-seven `have`s the first version
wrote are gone and the C proof is seventy-two lines instead of a hundred and
thirty-nine.

```c filename=sweep_maintains_a_zero_unmarked_count.c
void sweep(int32 visited[], int32 n) {
    for (int32 i = 0; i < n; i++) {
        visited[i] = 1;
    }
}
```

```click
verifying "sweep_maintains_a_zero_unmarked_count.c";

function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

theorem unmarked_frame(
    a: int32[],
    b: int32[],
    lo: int32,
    n: int32,
    m: int32,
    hi: int32
) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= m;
    requires m <= n;
    requires n <= 1073741823;
    views a[lo..n];
    views b[lo..n];
    requires forall (k: int32) {
        lo <= k and k < m implies a[k] == b[k]
    };
    ensures unmarked(a, lo, hi) == unmarked(b, lo, hi) by {
        induct(hi) as ih;
        if hi <= lo {
            unfold(unmarked(a, lo, hi)) using { hi <= lo; }
            unfold(unmarked(b, lo, hi)) using { hi <= lo; }
            simp();
        } else {
            have 0 <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
            have lo <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 <= m by { arithmetic() using { 0 <= lo; lo < hi; hi <= m; } }
            have hi - 1 < m by { arithmetic() using { 0 <= lo; lo < hi; hi <= m; } }
            have hi - 1 < 2147483647 by { arithmetic() using { 0 <= lo; lo < hi; } }
            apply(ih(hi - 1)) using {
                0 <= hi - 1;
                hi - 1 < hi;
                0 <= lo;
                hi - 1 <= m;
                m <= n;
                n <= 1073741823;
                viewable(a[lo..n]);
                viewable(b[lo..n]);
                forall (k: int32) { lo <= k and k < m implies a[k] == b[k] };
                0 <= n - lo;
                n - lo <= 1073741823;
            }
            have a[hi - 1] == b[hi - 1] by {
                instantiate(forall (k: int32) {
                    lo <= k and k < m implies a[k] == b[k]
                }, hi - 1) using { lo <= hi - 1; hi - 1 < m; }
                assumption();
            }
            unfold(unmarked(a, lo, hi)) using {
                lo <= hi - 1;
                hi - 1 < 2147483647;
            }
            unfold(unmarked(b, lo, hi)) using {
                lo <= hi - 1;
                hi - 1 < 2147483647;
            }
            have to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                == to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) by {
                simp() using { a[hi - 1] == b[hi - 1]; };
            }
            have unmarked(a, lo, hi - 1)
                + to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                == unmarked(b, lo, hi - 1)
                    + to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) by {
                arithmetic() using {
                    unmarked(a, lo, hi - 1) == unmarked(b, lo, hi - 1);
                    to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                        == to_integer(if b[hi - 1] == 0 { 1 } else { 0 });
                }
            }
            assumption();
        }
    }
}

void sweep(int32 visited[], int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    consumes visited[0..n];
    produces visited[0..n];
} by {
    step();
    step();
    have 0 <= 0 by { simp(); }
    have unmarked(visited, 0, 0) == 0 by {
        unfold(unmarked(visited, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant unmarked(visited, 0, i) == 0;
        owns visited[0..n];
        initialize by { simp(); }
        preserve by {
            mark iter;
            have i < 1073741823 by {
                arithmetic() using { i < n; n <= 1073741823; }
            }
            have i < 2147483647 by { arithmetic() using { i < 1073741823; } }
            step();
            have viewable(visited[0..n]) by { simp(); }
            have forall (k: int32) {
                0 <= k and k < i implies at(iter, visited[k]) == visited[k]
            } by {
                intro();
                intro();
                extract(k < i);
                have k != i by {
                    apply(int32_lt_implies_neq(k, i)) using { k < i; }
                    assumption();
                }
                have at(iter, visited[k]) == at(iter, visited[k]) by { normalize(); }
                transport(
                    at(iter, visited[k]) == at(iter, visited[k]),
                    at(iter, visited[k]) == visited[k]
                ) using {
                    at(iter, visited[k]) == at(iter, visited[k]);
                    k != i;
                };
                assumption();
            }
            have unmarked(at(iter, visited), 0, i) == unmarked(visited, 0, i) by {
                apply(unmarked_frame(at(iter, visited), visited, 0, n, i, i));
                assumption();
            }
            have unmarked(visited, 0, i) == 0 by {
                arithmetic() using {
                    unmarked(at(iter, visited), 0, i) == unmarked(visited, 0, i);
                    unmarked(at(iter, visited), 0, i) == 0;
                }
            }
            have unmarked(visited, 0, i + 1) == 0 by {
                unfold(unmarked(visited, 0, i + 1)) using {
                    0 <= (i + 1) - 1;
                    (i + 1) - 1 < 2147483647;
                }
                simp();
            }
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
