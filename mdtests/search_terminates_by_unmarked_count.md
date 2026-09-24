# A pointer-chasing search terminates on the number of unmarked cells

`next` holds quasi-pointers: every entry of `next[0..n]` is itself an index
into `0..n`. The search follows those entries, marking each cell it leaves,
and stops when it reaches a cell it has already marked.

Nothing about the indices decreases, so the loop measure is the number of
cells in `visited[0..n]` that still hold zero. The guard establishes that the
current cell contributes one; the body marks it and the point-update theorem
proves that the measure drops by exactly one. The proof also exercises an
early return inside the ranked loop and preserves the quantified bounds on the
pointer-chasing array. A ghost `Nat` witness tracks how many `next` hops reach
`cur`; its inductive frame lemma keeps that relation stable across each store
to the disjoint `visited` array. A result of `1` therefore names an in-bounds,
unmarked target reachable from `from` by a finite walk.

```c filename=search_terminates_by_unmarked_count.c
int32 search(int32 *next, int32 *visited, int32 n, int32 from, int32 to) {
    int32 cur = from;
    while (visited[cur] == 0) {
        if (cur == to) return 1;
        visited[cur] = 1;
        cur = next[cur];
    }
    return 0;
}
```

```click
verifying "search_terminates_by_unmarked_count.c";

function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

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

theorem walk_frame(a: int32[], b: int32[], n: int32, from: int32, fuel: Nat) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views a[0..n];
    views b[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= a[k] and a[k] < n
    };
    requires forall (k: int32) {
        0 <= k and k < n implies a[k] == b[k]
    };
    ensures walk(a, from, fuel) == walk(b, from, fuel) by {
        induct(fuel) as ih {
            Nat::Zero => {
                unfold(walk(a, from, Nat::Zero));
                unfold(walk(b, from, Nat::Zero));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                have 0 <= n by { arithmetic() using { 0 <= from; from < n; } }
                have 0 <= n - 0 by { arithmetic() using { 0 <= n; } }
                have n - 0 <= 1073741823 by {
                    arithmetic() using { n <= 1073741823; }
                }
                apply(walk_in_range(a, n, from, previous)) using {
                    0 <= from;
                    from < n;
                    n <= 1073741823;
                    viewable(a[0..n]);
                    forall (k: int32) {
                        0 <= k and k < n implies 0 <= a[k] and a[k] < n
                    };
                    0 <= n - 0;
                    n - 0 <= 1073741823;
                }
                have a[walk(a, from, previous)] == b[walk(a, from, previous)] by {
                    instantiate(forall (k: int32) {
                        0 <= k and k < n implies a[k] == b[k]
                    }, walk(a, from, previous)) using {
                        0 <= walk(a, from, previous);
                        walk(a, from, previous) < n;
                    }
                    assumption();
                }
                unfold(walk(a, from, Nat::Succ(previous)));
                unfold(walk(b, from, Nat::Succ(previous)));
                simp() using {
                    walk(a, from, previous) == walk(b, from, previous);
                    a[walk(a, from, previous)] == b[walk(a, from, previous)];
                }
            }
        }
    }
}

theorem unmarked_nonnegative(v: int32[], lo: int32, n: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires n <= 1073741823;
    views v[lo..n];
    ensures 0 <= unmarked(v, lo, hi) by {
        induct(hi) as ih;
        if hi <= lo {
            unfold(unmarked(v, lo, hi)) using { hi <= lo; }
            simp();
        } else {
            have 0 <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 <= n by { arithmetic() using { 0 <= lo; lo < hi; hi <= n; } }
            apply(ih(hi - 1)) using {
                0 <= hi - 1;
                hi - 1 < hi;
                0 <= lo;
                hi - 1 <= n;
                n <= 1073741823;
                viewable(v[lo..n]);
                0 <= n - lo;
                n - lo <= 1073741823;
            }
            have lo <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < 2147483647 by { arithmetic() using { 0 <= lo; lo < hi; } }
            unfold(unmarked(v, lo, hi)) using {
                lo <= hi - 1;
                hi - 1 < 2147483647;
            }
            have 0 <= (if v[hi - 1] == 0 { 1 } else { 0 }) by { simp(); }
            apply(int32_less_equal_to_integer(0, if v[hi - 1] == 0 { 1 } else { 0 })) using {
                0 <= (if v[hi - 1] == 0 { 1 } else { 0 });
            }
            have 0 <= unmarked(v, lo, hi - 1)
                + to_integer(if v[hi - 1] == 0 { 1 } else { 0 }) by {
                arithmetic() using {
                    0 <= unmarked(v, lo, hi - 1);
                    to_integer(0) <= to_integer(if v[hi - 1] == 0 { 1 } else { 0 });
                }
            }
            assumption();
        }
    }
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

theorem unmarked_point_update(
    a: int32[],
    b: int32[],
    lo: int32,
    n: int32,
    hi: int32,
    j: int32
) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires n <= 1073741823;
    views a[lo..n];
    views b[lo..n];
    requires lo <= j;
    requires j < hi;
    requires a[j] == 0;
    requires b[j] != 0;
    requires forall (k: int32) {
        lo <= k and k < j implies a[k] == b[k]
    };
    requires forall (k: int32) {
        j < k and k < n implies a[k] == b[k]
    };
    ensures unmarked(b, lo, hi) == unmarked(a, lo, hi) - 1 by {
        induct(hi) as ih;
        if hi <= lo {
            have j < lo by { arithmetic() using { j < hi; hi <= lo; } }
            contradiction(lo <= j);
        } else {
            have 0 <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
            have lo <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 <= n by { arithmetic() using { 0 <= lo; lo < hi; hi <= n; } }
            have hi - 1 < n by { arithmetic() using { 0 <= lo; lo < hi; hi <= n; } }
            have hi - 1 < 2147483647 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have j <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; j < hi; } }
            if j == hi - 1 {
                have j < n by { arithmetic() using { j < hi; hi <= n; } }
                have j <= n by { arithmetic() using { j < n; } }
                have hi - 1 <= j by {
                    arithmetic() using { 0 <= lo; lo < hi; j == hi - 1; }
                }
                apply(unmarked_frame(a, b, lo, n, j, hi - 1)) using {
                    0 <= lo;
                    0 <= hi - 1;
                    hi - 1 <= j;
                    j <= n;
                    n <= 1073741823;
                    viewable(a[lo..n]);
                    viewable(b[lo..n]);
                    forall (k: int32) { lo <= k and k < j implies a[k] == b[k] };
                    0 <= n - lo;
                    n - lo <= 1073741823;
                }
                have a[hi - 1] == 0 by { simp() using { a[j] == 0; j == hi - 1; }; }
                have b[hi - 1] != 0 by { simp() using { b[j] != 0; j == hi - 1; }; }
                unfold(unmarked(a, lo, hi)) using {
                    lo <= hi - 1;
                    hi - 1 < 2147483647;
                }
                unfold(unmarked(b, lo, hi)) using {
                    lo <= hi - 1;
                    hi - 1 < 2147483647;
                }
                have (if a[hi - 1] == 0 { 1 } else { 0 }) == 1 by {
                    normalize() using { a[hi - 1] == 0; }
                }
                have (if b[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                    normalize() using { b[hi - 1] != 0; }
                }
                have to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 1 by {
                    simp() using { (if a[hi - 1] == 0 { 1 } else { 0 }) == 1; };
                }
                have to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                    simp() using { (if b[hi - 1] == 0 { 1 } else { 0 }) == 0; };
                }
                have unmarked(b, lo, hi - 1)
                    + to_integer(if b[hi - 1] == 0 { 1 } else { 0 })
                    == unmarked(a, lo, hi - 1)
                        + to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) - 1 by {
                    arithmetic() using {
                        unmarked(a, lo, hi - 1) == unmarked(b, lo, hi - 1);
                        to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 1;
                        to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 0;
                    }
                }
                assumption();
            } else {
                have j < hi - 1 by {
                    apply(int32_le_and_neq_implies_lt(j, hi - 1)) using {
                        j <= hi - 1;
                        j != hi - 1;
                    }
                    assumption();
                }
                apply(ih(hi - 1)) using {
                    0 <= hi - 1;
                    hi - 1 < hi;
                    0 <= lo;
                    hi - 1 <= n;
                    n <= 1073741823;
                    viewable(a[lo..n]);
                    viewable(b[lo..n]);
                    lo <= j;
                    j < hi - 1;
                    a[j] == 0;
                    b[j] != 0;
                    forall (k: int32) { lo <= k and k < j implies a[k] == b[k] };
                    forall (k: int32) { j < k and k < n implies a[k] == b[k] };
                    0 <= n - lo;
                    n - lo <= 1073741823;
                }
                have a[hi - 1] == b[hi - 1] by {
                    instantiate(forall (k: int32) {
                        j < k and k < n implies a[k] == b[k]
                    }, hi - 1) using { j < hi - 1; hi - 1 < n; }
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
                have unmarked(b, lo, hi - 1)
                    + to_integer(if b[hi - 1] == 0 { 1 } else { 0 })
                    == unmarked(a, lo, hi - 1)
                        + to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) - 1 by {
                    arithmetic() using {
                        unmarked(b, lo, hi - 1) == unmarked(a, lo, hi - 1) - 1;
                        to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                            == to_integer(if b[hi - 1] == 0 { 1 } else { 0 });
                    }
                }
                assumption();
            }
        }
    }
}

int32 search(int32 *next, int32 *visited, int32 n, int32 from, int32 to) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views next[0..n];
    consumes visited[0..n];
    produces visited[0..n];
    requires separate(memory(next[0..n]), memory(visited[0..n]));
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k] and next[k] < n
    };
    ensures result == 1 implies
        0 <= to and to < n and visited[to] == 0;
    ensures result == 1 implies
        exists (fuel: Nat) { walk(next, from, fuel) == to };
} by {
    step();
    step();
    have exists (fuel: Nat) { walk(next, from, fuel) == cur } by {
        witness(fuel = Nat::Zero);
        unfold(walk(next, from, Nat::Zero));
        simp();
    }
    loop {
        decreases unmarked(visited, 0, n);
        invariant 0 <= cur;
        invariant cur < n;
        invariant forall (k: int32) {
            0 <= k and k < n implies 0 <= next[k] and next[k] < n
        };
        invariant exists (fuel: Nat) { walk(next, from, fuel) == cur };
        views next[0..n];
        owns visited[0..n];
        initialize by { simp(); }
        preserve by {
            mark iter;
            let (previous: Nat) satisfy { walk(next, from, previous) == cur };
            have 0 <= 0 by { simp(); }
            have n <= n by { simp(); }
            have 0 <= n by { arithmetic() using { 0 <= cur; cur < n; } }
            have 0 <= next[cur] and next[cur] < n by {
                instantiate(forall (k: int32) {
                    0 <= k and k < n implies 0 <= next[k] and next[k] < n
                }, cur) using { 0 <= cur; cur < n; }
                assumption();
            }
            if cur == to {
                step();
                step();
                simp();
            } else {
                step();
            }
            step();
            step();
            have forall (k: int32) {
                0 <= k and k < n implies at(iter, next[k]) == next[k]
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < n);
                have at(iter, next[k]) == at(iter, next[k]) by { normalize(); }
                transport(
                    at(iter, next[k]) == at(iter, next[k]),
                    at(iter, next[k]) == next[k]
                ) using {
                    at(iter, next[k]) == at(iter, next[k]);
                    0 <= k;
                    k < n;
                    0 <= cur;
                    cur < n;
                    separate(memory(next[0..n]), memory(visited[0..n]));
                }
                assumption();
            }
            have forall (k: int32) {
                0 <= k and k < cur implies at(iter, visited[k]) == visited[k]
            } by {
                intro();
                intro();
                extract(k < cur);
                have k != cur by {
                    apply(int32_lt_implies_neq(k, cur)) using { k < cur; }
                    assumption();
                }
                have at(iter, visited[k]) == at(iter, visited[k]) by { normalize(); }
                transport(
                    at(iter, visited[k]) == at(iter, visited[k]),
                    at(iter, visited[k]) == visited[k]
                ) using {
                    at(iter, visited[k]) == at(iter, visited[k]);
                    k != cur;
                };
                assumption();
            }
            have forall (k: int32) {
                cur < k and k < n implies at(iter, visited[k]) == visited[k]
            } by {
                intro();
                intro();
                extract(cur < k);
                have cur != k by {
                    apply(int32_lt_implies_neq(cur, k)) using { cur < k; }
                    assumption();
                }
                have at(iter, visited[k]) == at(iter, visited[k]) by { normalize(); }
                transport(
                    at(iter, visited[k]) == at(iter, visited[k]),
                    at(iter, visited[k]) == visited[k]
                ) using {
                    at(iter, visited[k]) == at(iter, visited[k]);
                    cur != k;
                };
                assumption();
            }
            have at(iter, visited[cur]) == 0 by { simp(); }
            have visited[cur] != 0 by { simp(); }
            have viewable(visited[0..n]) by { simp(); }
            have at(iter, viewable(visited[0..n])) by { simp(); }
            apply(unmarked_point_update(at(iter, visited), visited, 0, n, n, cur)) using {
                0 <= 0;
                0 <= n;
                n <= n;
                n <= 1073741823;
                at(iter, viewable(visited[0..n]));
                viewable(visited[0..n]);
                0 <= cur;
                cur < n;
                at(iter, visited[cur]) == 0;
                visited[cur] != 0;
                forall (k: int32) {
                    0 <= k and k < cur implies at(iter, visited[k]) == visited[k]
                };
                forall (k: int32) {
                    cur < k and k < n implies at(iter, visited[k]) == visited[k]
                };
                0 <= n - 0;
                n - 0 <= 1073741823;
            }
            apply(unmarked_nonnegative(visited, 0, n, n)) using {
                0 <= 0;
                0 <= n;
                n <= n;
                n <= 1073741823;
                viewable(visited[0..n]);
                0 <= n - 0;
                n - 0 <= 1073741823;
            }
            have unmarked(visited, 0, n) < unmarked(at(iter, visited), 0, n) by {
                arithmetic() using {
                    unmarked(visited, 0, n) == unmarked(at(iter, visited), 0, n) - 1;
                }
            }
            step();
            have at(iter, walk(next, from, previous)) == at(iter, cur) by {
                simp();
            }
            have at(iter, viewable(next[0..n])) by { simp(); }
            have viewable(next[0..n]) by { simp(); }
            have forall (k: int32) {
                0 <= k and k < n implies
                    0 <= at(iter, next[k]) and at(iter, next[k]) < n
            } by { simp(); }
            apply(walk_frame(at(iter, next), next, n, from, previous)) using {
                0 <= from;
                from < n;
                n <= 1073741823;
                at(iter, viewable(next[0..n]));
                viewable(next[0..n]);
                forall (k: int32) {
                    0 <= k and k < n implies
                        0 <= at(iter, next[k]) and at(iter, next[k]) < n
                };
                forall (k: int32) {
                    0 <= k and k < n implies at(iter, next[k]) == next[k]
                };
                0 <= n - 0;
                n - 0 <= 1073741823;
            }
            have walk(next, from, previous) == at(iter, cur) by {
                simp() using {
                    at(iter, walk(next, from, previous)) == at(iter, cur);
                    walk(at(iter, next), from, previous) == walk(next, from, previous);
                }
            }
            have forall (k: int32) {
                0 <= k and k < n implies 0 <= next[k] and next[k] < n
            } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < n);
                have 0 <= at(iter, next[k]) and at(iter, next[k]) < n by {
                    instantiate(forall (j: int32) {
                        0 <= j and j < n implies
                            0 <= at(iter, next[j]) and at(iter, next[j]) < n
                    }, k) using { 0 <= k; k < n; }
                    assumption();
                }
                have at(iter, next[k]) == next[k] by {
                    instantiate(forall (j: int32) {
                        0 <= j and j < n implies at(iter, next[j]) == next[j]
                    }, k) using { 0 <= k; k < n; }
                    assumption();
                }
                rewrite(next[k] == at(iter, next[k]));
                assumption();
            }
            apply(walk_in_range(next, n, from, previous)) using {
                0 <= from;
                from < n;
                n <= 1073741823;
                viewable(next[0..n]);
                forall (k: int32) {
                    0 <= k and k < n implies 0 <= next[k] and next[k] < n
                };
                0 <= n - 0;
                n - 0 <= 1073741823;
            }
            have next[walk(next, from, previous)] == next[at(iter, cur)] by {
                simp() using { walk(next, from, previous) == at(iter, cur); }
            }
            have next[at(iter, cur)] == cur by { simp(); }
            have exists (fuel: Nat) { walk(next, from, fuel) == cur } by {
                witness(fuel = Nat::Succ(previous));
                unfold(walk(next, from, Nat::Succ(previous)));
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
