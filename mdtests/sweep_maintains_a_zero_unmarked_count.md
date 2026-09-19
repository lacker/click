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
`transport ... using` per cell under two `intro()`s.

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
    requires n >= 0 and loadable(a[lo..n]);
    requires n >= 0 and loadable(b[lo..n]);
    requires forall (k: int32) {
        lo <= k and k < m implies a[k] == b[k]
    };
    ensures unmarked(a, lo, hi) == unmarked(b, lo, hi) by {
        induct(hi) as ih;
        if hi <= lo {
            unfold(unmarked(a, lo, hi)) using {
                hi <= lo;
            }
            unfold(unmarked(b, lo, hi)) using {
                hi <= lo;
            }
            simp();
        } else {
            have lo < hi by { simp(); }
            have 0 <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
            have lo <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 <= m by { arithmetic() using { 0 <= lo; lo < hi; hi <= m; } }
            have hi - 1 < m by { arithmetic() using { 0 <= lo; lo < hi; hi <= m; } }
            have lo < m by { arithmetic() using { lo < hi; hi <= m; } }
            have lo < n by { arithmetic() using { lo < m; m <= n; } }
            have 0 <= n - lo by {
                arithmetic() using { 0 <= lo; lo < n; n <= 1073741823; }
            }
            have n - lo <= 1073741823 by {
                arithmetic() using { 0 <= lo; lo < n; n <= 1073741823; }
            }
            apply(ih(hi - 1)) using {
                0 <= hi - 1;
                hi - 1 < hi;
                0 <= lo;
                hi - 1 <= m;
                m <= n;
                n <= 1073741823;
                n >= 0 and loadable(a[lo..n]);
                n >= 0 and loadable(b[lo..n]);
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
            have hi - 1 < 2147483647 by { arithmetic() using { 0 <= lo; lo < hi; } }
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
            arithmetic_certificate {
                premise 0: unmarked(a, lo, hi - 1) == unmarked(b, lo, hi - 1) =>
                    unmarked(a, lo, hi - 1) == unmarked(b, lo, hi - 1);
                premise 1: to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                    == to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) =>
                    to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                        == to_integer(if b[hi - 1] == 0 { 1 } else { 0 });
                eq_to_le 0 => unmarked(a, lo, hi - 1) <= unmarked(b, lo, hi - 1);
                eq_to_le 0 reverse => unmarked(b, lo, hi - 1) <= unmarked(a, lo, hi - 1);
                eq_to_le 1 => to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                    <= to_integer(if b[hi - 1] == 0 { 1 } else { 0 });
                eq_to_le 1 reverse => to_integer(if b[hi - 1] == 0 { 1 } else { 0 })
                    <= to_integer(if a[hi - 1] == 0 { 1 } else { 0 });
                add 2, 4 => unmarked(a, lo, hi - 1) + to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                    <= unmarked(b, lo, hi - 1) + to_integer(if b[hi - 1] == 0 { 1 } else { 0 });
                add 3, 5 => unmarked(b, lo, hi - 1) + to_integer(if b[hi - 1] == 0 { 1 } else { 0 })
                    <= unmarked(a, lo, hi - 1) + to_integer(if a[hi - 1] == 0 { 1 } else { 0 });
                eq_from_bounds 6, 7 =>
                    unmarked(a, lo, hi - 1) + to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                        == unmarked(b, lo, hi - 1) + to_integer(if b[hi - 1] == 0 { 1 } else { 0 });
                conclusion 8;
            }
        }
    }
}

void sweep(int32 visited[], int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    requires loadable(visited[0..n]);
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
            have 0 <= i by { simp(); }
            have i <= n by { simp(); }
            have i < n by { simp(); }
            have i < 1073741823 by {
                arithmetic() using { i < n; n <= 1073741823; }
            }
            have i <= 1073741823 by { arithmetic() using { i < 1073741823; } }
            have i < 2147483647 by { arithmetic() using { i < 1073741823; } }
            have i >= 0 by { arithmetic() using { 0 <= i; } }
            have i <= i by { simp(); }
            have 0 <= i - 0 by { arithmetic() using { 0 <= i; } }
            have i - 0 <= 1073741823 by {
                arithmetic() using { i <= 1073741823; }
            }
            have 0 <= 0 by { simp(); }
            have 0 <= n - 0 by { arithmetic() using { 0 <= n; } }
            have n - 0 <= 1073741823 by {
                arithmetic() using { n <= 1073741823; }
            }
            have n >= 0 by { arithmetic() using { 0 <= n; } }
            have loadable(visited[0..n]) by { simp(); }
            have n >= 0 and loadable(visited[0..n]) by { split(); }
            step();
            have loadable(visited[0..n]) by { simp(); }
            have n >= 0 and loadable(visited[0..n]) by { split(); }
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
                arithmetic_certificate {
                    premise 0: unmarked(at(iter, visited), 0, i)
                        == unmarked(visited, 0, i) =>
                        unmarked(at(iter, visited), 0, i) == unmarked(visited, 0, i);
                    premise 1: unmarked(at(iter, visited), 0, i) == 0 =>
                        unmarked(at(iter, visited), 0, i) == 0;
                    eq_to_le 0 reverse =>
                        unmarked(visited, 0, i) <= unmarked(at(iter, visited), 0, i);
                    eq_to_le 1 => unmarked(at(iter, visited), 0, i) <= 0;
                    add 2, 3 => unmarked(visited, 0, i) <= 0;
                    eq_to_le 0 =>
                        unmarked(at(iter, visited), 0, i) <= unmarked(visited, 0, i);
                    eq_to_le 1 reverse => 0 <= unmarked(at(iter, visited), 0, i);
                    add 6, 5 => 0 <= unmarked(visited, 0, i);
                    eq_from_bounds 4, 7 => unmarked(visited, 0, i) == 0;
                    conclusion 8;
                }
            }
            have visited[i] == 1 by { simp(); }
            have visited[i] != 0 by { simp() using { visited[i] == 1; }; }
            have (if visited[i] == 0 { 1 } else { 0 }) == 0 by {
                normalize() using { visited[i] != 0; }
            }
            have to_integer(if visited[i] == 0 { 1 } else { 0 }) == 0 by {
                simp() using { (if visited[i] == 0 { 1 } else { 0 }) == 0; };
            }
            have 0 <= i + 1 by {
                apply(int32_increment_lower_bound(i, 0, n)) using { 0 <= i; i < n; }
                assumption();
            }
            have defined(i + 1) by {
                apply(int32_increment_below_max_is_defined(i));
                assumption();
            }
            have i + 1 <= n by {
                apply(int32_increment_upper_bound(i, n)) using { i < n; }
                assumption();
            }
            have i + 1 <= 1073741823 by {
                apply(int32_le_transitive(i + 1, n, 1073741823)) using {
                    i + 1 <= n;
                    n <= 1073741823;
                }
                assumption();
            }
            have 0 <= i + 1 - 0 by { arithmetic() using { 0 <= i + 1; } }
            have i + 1 - 0 <= 1073741823 by {
                arithmetic() using { i + 1 <= 1073741823; }
            }
            have unmarked(visited, 0, i + 1) == 0 by {
                unfold(unmarked(visited, 0, i + 1)) using {
                    0 <= (i + 1) - 1;
                    (i + 1) - 1 < 2147483647;
                }
                simp();
            }
            step();
            have i == at(iter, i) + 1 by { simp(); }
            have unmarked(visited, 0, i) == 0 by {
                rewrite(i == at(iter, i) + 1);
                assumption();
            }
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
