# a pointer-chasing search terminates on the number of unmarked cells

**BLOCKED — this file has not yet been shown to verify completely.** Updated on
2026-09-22 after repairing ranked-loop return paths and correcting the false
arm's execution cursor. Both halves of the quantified invariant over `next`
now close. The earlier `visited[cur] != 0` refusal occurred before the store:
the proof had crossed the lowered empty-`else` `Skip`, but not the following
`visited[cur] = 1`. The extra `step()` below crosses the store, and
`mdtests/post_store_fact_after_ranked_loop_return.md` checks both the equality
and disequality at that exact control shape. The complete proof still needs a
fresh ordinary verification run to locate its next genuine open obligation.
The earlier range-narrowing defect was fixed in `88b05d28`, with regression
`mdtests/a_second_universal_have_narrows_a_stated_range.md`; it is not the
remaining prerequisite. See `issues/dfs.md` for the current handoff checkpoint.
Do not move this file into `mdtests/` until the complete proof verifies.


`next` holds quasi-pointers: every entry of `next[0..n]` is itself an index
into `0..n`. `search` follows them from `from`, marking each cell it leaves,
and stops when it reaches a cell it has already marked. Nothing about the
indices decreases — the walk may revisit any cell — so the measure is the
number of cells of `visited[0..n]` that still hold zero, which the body drops
by one every iteration because the guard says `visited[cur]` was zero and the
body writes it.

`decreases` takes the `Integer`-valued fold directly, and the ranking bundle
it adds is `0 <= unmarked(visited, 0, n)` at the back edge and a strict
decrease there. The three theorems are the ones that bundle needs:
`unmarked_nonnegative` for the first member, `unmarked_point_update` for the
second, and `unmarked_frame`, which the point update calls at its boundary
case. They are copies of `mdtests/unmarked_count_lemmas.md`, because an
`import` assumes a theorem's proof rather than checking it.

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
    requires below: forall (k: int32) {
        lo <= k and k < j implies a[k] == b[k]
    };
    requires above: forall (k: int32) {
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
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k] and next[k] < n
    };
} by {
    step();
    step();
    loop {
        decreases unmarked(visited, 0, n);
        invariant 0 <= cur;
        invariant cur < n;
        invariant forall (k: int32) {
            0 <= k and k < n implies 0 <= next[k] and next[k] < n
        };
        views next[0..n];
        owns visited[0..n];
        initialize by { simp(); }
        preserve by {
            mark iter;
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
            } else {
                step();
            }
            step();
            step();
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
            close_invariants();
        }
    }
    execute();
    simp();
}
```

The former `visited[cur] != 0` diagnostic was a proof-cursor mistake, not a
post-store failure. The false C arm lowers through an explicit `Skip`, so the
proof needs one step to select that arm, one to execute the `Skip`, and one to
execute the store before stating its result. The focused regression is
`mdtests/post_store_fact_after_ranked_loop_return.md`.

The quantified value and viewability leaves also close; the pointer-chasing
value route is covered by
`mdtests/loop_quantified_value_after_pointer_chase.md`. See the current
checkpoint in `issues/dfs.md`. The explicit transport limitation remains
independently reproduced in `a_universal_fact_does_not_transport.md`.
