# A cyclic, two-successor graph search

The C is the graph search from `design/dfs-gaps/branching_graph_dfs.md`, unchanged.
Both successor arrays are bounded and read-only; `visited` is mutable. The
number of unmarked cells ranks both recursive calls, including the right call
after the left call may have marked additional nodes. The recursive contract
also preserves every previously marked node. A nonzero result supplies a
finite left/right path in the entry graph and proves the target was in bounds
and unmarked at entry. Both recursive success branches construct and frame
their witnesses; no claim of failure-path completeness is made.

```c filename=branching_graph_dfs.c
int32 dfs(int32 *left, int32 *right, int32 *visited,
          int32 n, int32 cur, int32 to) {
    if (visited[cur] != 0) return 0;
    if (cur == to) return 1;
    visited[cur] = 1;
    if (dfs(left, right, visited, n, left[cur], to)) return 1;
    return dfs(left, right, visited, n, right[cur], to);
}
```

```click
verifying "branching_graph_dfs.c";

function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

spec enum Path {
    Here,
    Left(Path),
    Right(Path),
}

function walk(left: int32[], right: int32[], from: int32, path: Path) -> int32
    decreases path
{
    match path {
        Path::Here => from,
        Path::Left(rest) => walk(left, right, left[from], rest),
        Path::Right(rest) => walk(left, right, right[from], rest),
    }
}

theorem walk_frame(a: int32[], b: int32[], c: int32[], d: int32[], n: int32, from: int32, path: Path) {
    requires 0 <= from;
    requires from < n;
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= a[k] and a[k] < n };
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= b[k] and b[k] < n };
    requires forall (k: int32) { 0 <= k and k < n implies a[k] == c[k] };
    requires forall (k: int32) { 0 <= k and k < n implies b[k] == d[k] };
    ensures walk(a, b, from, path) == walk(c, d, from, path) by {
        induct(path) as ih {
            Path::Here => {
                unfold(walk(a, b, from, Path::Here));
                unfold(walk(c, d, from, Path::Here));
                normalize();
            }
            Path::Left(rest) => {
                have 0 <= a[from] and a[from] < n by {
                    instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= a[k] and a[k] < n }, from) using { 0 <= from; from < n; }
                    assumption();
                }
                have a[from] == c[from] by {
                    instantiate(forall (k: int32) { 0 <= k and k < n implies a[k] == c[k] }, from) using { 0 <= from; from < n; }
                    assumption();
                }
                apply(ih(a, b, c, d, n, a[from], rest));
                unfold(walk(a, b, from, Path::Left(rest)));
                unfold(walk(c, d, from, Path::Left(rest)));
                simp() using {
                    a[from] == c[from];
                    walk(a, b, a[from], rest) == walk(c, d, a[from], rest);
                }
            }
            Path::Right(rest) => {
                have 0 <= b[from] and b[from] < n by {
                    instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= b[k] and b[k] < n }, from) using { 0 <= from; from < n; }
                    assumption();
                }
                have b[from] == d[from] by {
                    instantiate(forall (k: int32) { 0 <= k and k < n implies b[k] == d[k] }, from) using { 0 <= from; from < n; }
                    assumption();
                }
                apply(ih(a, b, c, d, n, b[from], rest));
                unfold(walk(a, b, from, Path::Right(rest)));
                unfold(walk(c, d, from, Path::Right(rest)));
                simp() using {
                    b[from] == d[from];
                    walk(a, b, b[from], rest) == walk(c, d, b[from], rest);
                }
            }
        }
    }
}

resource bounded_successors(left: int32*, right: int32*, n: int32) {
    views left[0..n];
    views right[0..n];
    fact forall (k: int32) {
        0 <= k and k < n implies 0 <= left[k] and left[k] < n
    };
    fact forall (k: int32) {
        0 <= k and k < n implies 0 <= right[k] and right[k] < n
    };
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

theorem marked_transitive(a: int32[], b: int32[], c: int32[], n: int32) {
    requires forall (k: int32) { 0 <= k and k < n and a[k] != 0 implies b[k] != 0 };
    requires forall (k: int32) { 0 <= k and k < n and b[k] != 0 implies c[k] != 0 };
    ensures forall (k: int32) { 0 <= k and k < n and a[k] != 0 implies c[k] != 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < n);
        extract(a[k] != 0);
        instantiate(forall (k: int32) { 0 <= k and k < n and a[k] != 0 implies b[k] != 0 }, k) using { 0 <= k; k < n; a[k] != 0; }
        instantiate(forall (k: int32) { 0 <= k and k < n and b[k] != 0 implies c[k] != 0 }, k) using { 0 <= k; k < n; b[k] != 0; }
        assumption();
    }
}

int32 dfs(int32 *left, int32 *right, int32 *visited,
          int32 n, int32 cur, int32 to) {
    decreases unmarked(visited, 0, n);
    requires 0 <= cur;
    requires cur < n;
    requires n <= 1073741823;
    views bounded_successors(left, right, n);
    owns visited[0..n];
    requires separate(memory(left[0..n]), memory(visited[0..n]));
    requires separate(memory(right[0..n]), memory(visited[0..n]));
    ensures unmarked(visited, 0, n) <= old(unmarked(visited, 0, n));
    ensures result != 0 implies exists (path: Path) {
        walk(old(left), old(right), cur, path) == to
    };
    ensures result != 0 implies 0 <= to and to < n and old(visited[to]) == 0;
    ensures forall (k: int32) {
        0 <= k and k < n and old(visited[k]) != 0 implies visited[k] != 0
    };
} by {
    observe(bounded_successors(left, right, n));
    have forall (k: int32) {
        0 <= k and k < n implies 0 <= old(left[k]) and old(left[k]) < n
    } by { assumption(); }
    have forall (k: int32) {
        0 <= k and k < n implies 0 <= old(right[k]) and old(right[k]) < n
    } by { assumption(); }

    branch {
        then {
            have forall (k: int32) {
                0 <= k and k < n and old(visited[k]) != 0 implies visited[k] != 0
            } by { intro(); intro(); simp(); }
            step();
            simp();
        }
        else {}
    }
    branch {
        then {
            have exists (path: Path) { walk(old(left), old(right), cur, path) == to } by {
                witness(path = Path::Here);
                unfold(walk(old(left), old(right), cur, Path::Here));
                simp();
            }
            have 0 <= to and to < n and old(visited[to]) == 0 by {
                have to == cur by { simp(); }
                rewrite(to == cur);
                simp();
            }
            have forall (k: int32) {
                0 <= k and k < n and old(visited[k]) != 0 implies visited[k] != 0
            } by { intro(); intro(); simp(); }
            step();
            simp();
        }
        else {}
    }
    mark before_mark;
    step();
    have forall (k: int32) {
        0 <= k and k < n and old(visited[k]) != 0 implies visited[k] != 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < n);
        extract(old(visited[k]) != 0);
        if k == cur {
            have visited[cur] == 1 by { simp(); }
            rewrite(k == cur);
            simp();
        } else {
            have old(visited[k]) == at(before_mark, visited[k]) by { normalize(); }
            transport(old(visited[k]) == at(before_mark, visited[k]), old(visited[k]) == visited[k]) using {
                old(visited[k]) == at(before_mark, visited[k]);
                0 <= k; k < n; k != cur;
            };
            simp() using { old(visited[k]) != 0; old(visited[k]) == visited[k]; }
        }
    }

    have 0 <= 0 by { simp(); }
    have n <= n by { simp(); }
    have 0 <= n by { arithmetic() using { 0 <= cur; cur < n; } }
    have forall (k: int32) {
        0 <= k and k < cur implies at(before_mark, visited[k]) == visited[k]
    } by {
        intro();
        intro();
        extract(k < cur);
        have k != cur by {
            apply(int32_lt_implies_neq(k, cur)) using { k < cur; }
            assumption();
        }
        have at(before_mark, visited[k]) == at(before_mark, visited[k]) by { normalize(); }
        transport(
            at(before_mark, visited[k]) == at(before_mark, visited[k]),
            at(before_mark, visited[k]) == visited[k]
        ) using {
            at(before_mark, visited[k]) == at(before_mark, visited[k]);
            k != cur;
        };
        assumption();
    }
    have forall (k: int32) {
        cur < k and k < n implies at(before_mark, visited[k]) == visited[k]
    } by {
        intro();
        intro();
        extract(cur < k);
        have cur != k by {
            apply(int32_lt_implies_neq(cur, k)) using { cur < k; }
            assumption();
        }
        have at(before_mark, visited[k]) == at(before_mark, visited[k]) by { normalize(); }
        transport(
            at(before_mark, visited[k]) == at(before_mark, visited[k]),
            at(before_mark, visited[k]) == visited[k]
        ) using {
            at(before_mark, visited[k]) == at(before_mark, visited[k]);
            cur != k;
        };
        assumption();
    }
    have at(before_mark, visited[cur]) == 0 by { simp(); }
    have visited[cur] != 0 by { simp(); }
    have viewable(visited[0..n]) by { simp(); }
    have at(before_mark, viewable(visited[0..n])) by { simp(); }
    apply(unmarked_point_update(at(before_mark, visited), visited, 0, n, n, cur)) using {
        0 <= 0;
        0 <= n;
        n <= n;
        n <= 1073741823;
        at(before_mark, viewable(visited[0..n]));
        viewable(visited[0..n]);
        0 <= cur;
        cur < n;
        at(before_mark, visited[cur]) == 0;
        visited[cur] != 0;
        forall (k: int32) {
            0 <= k and k < cur implies at(before_mark, visited[k]) == visited[k]
        };
        forall (k: int32) {
            cur < k and k < n implies at(before_mark, visited[k]) == visited[k]
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
    have 0 <= unmarked(visited, 0, n) by { assumption(); }
    have unmarked(visited, 0, n) < unmarked(at(before_mark, visited), 0, n) by {
        arithmetic() using {
            unmarked(visited, 0, n) == unmarked(at(before_mark, visited), 0, n) - 1;
        }
    }
    have unmarked(at(before_mark, visited), 0, n) == old(unmarked(visited, 0, n)) by {
        simp();
    }
    have unmarked(visited, 0, n) < old(unmarked(visited, 0, n)) by {
        arithmetic() using {
            unmarked(visited, 0, n) < unmarked(at(before_mark, visited), 0, n);
            unmarked(at(before_mark, visited), 0, n) == old(unmarked(visited, 0, n));
        }
    }
    observe(bounded_successors(left, right, n));
    have 0 <= left[cur] and left[cur] < n by {
        instantiate(forall (k: int32) {
            0 <= k and k < n implies 0 <= left[k] and left[k] < n
        }, cur) using { 0 <= cur; cur < n; }
        assumption();
    }
    mark after_mark;
    have forall (k: int32) {
        0 <= k and k < n implies old(left[k]) == at(after_mark, left[k])
    } by {
        intro(); intro();
        extract(0 <= k); extract(k < n);
        have old(left[k]) == old(left[k]) by { normalize(); }
        transport(old(left[k]) == old(left[k]), old(left[k]) == at(after_mark, left[k])) using {
            old(left[k]) == old(left[k]);
            0 <= k; k < n;
            separate(memory(left[0..n]), memory(visited[0..n]));
        };
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < n implies old(right[k]) == at(after_mark, right[k])
    } by {
        intro(); intro();
        extract(0 <= k); extract(k < n);
        have old(right[k]) == old(right[k]) by { normalize(); }
        transport(old(right[k]) == old(right[k]), old(right[k]) == at(after_mark, right[k])) using {
            old(right[k]) == old(right[k]);
            0 <= k; k < n;
            separate(memory(right[0..n]), memory(visited[0..n]));
        };
        assumption();
    }

    have forall (k: int32) {
        0 <= k and k < n and old(visited[k]) != 0 implies at(after_mark, visited[k]) != 0
    } by { assumption(); }
    let left_result = step(dfs(left, right, visited, n, left[cur], to), {});
    have forall (k: int32) {
        0 <= k and k < n and at(after_mark, visited[k]) != 0 implies visited[k] != 0
    } by { assumption(); }
    apply(marked_transitive(old(visited), at(after_mark, visited), visited, n)) using {
        forall (k: int32) { 0 <= k and k < n and old(visited[k]) != 0 implies at(after_mark, visited[k]) != 0 };
        forall (k: int32) { 0 <= k and k < n and at(after_mark, visited[k]) != 0 implies visited[k] != 0 };
    }

    have unmarked(visited, 0, n) <= unmarked(at(after_mark, visited), 0, n) by {
        simp();
    }
    have unmarked(at(after_mark, visited), 0, n)
        == unmarked(at(before_mark, visited), 0, n) - 1 by {
        simp();
    }
    have unmarked(visited, 0, n) <= old(unmarked(visited, 0, n)) by {
        arithmetic() using {
            unmarked(visited, 0, n) <= unmarked(at(after_mark, visited), 0, n);
            unmarked(at(after_mark, visited), 0, n)
                == unmarked(at(before_mark, visited), 0, n) - 1;
            unmarked(at(before_mark, visited), 0, n)
                == old(unmarked(visited, 0, n));
        }
    }
    branch {
        then {
            have left_result != 0 implies exists (path: Path) {
                walk(at(after_mark, left), at(after_mark, right), at(after_mark, left[cur]), path) == to
            } by { assumption(); }
            have exists (path: Path) {
                walk(at(after_mark, left), at(after_mark, right), at(after_mark, left[cur]), path) == to
            } by { simp(); }
            let (rest: Path) satisfy {
                walk(at(after_mark, left), at(after_mark, right), at(after_mark, left[cur]), rest) == to
            };
            have walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest)) == to by {
                unfold(walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest)));
                assumption();
            }
            apply(walk_frame(old(left), old(right), at(after_mark, left), at(after_mark, right), n, cur, Path::Left(rest))) using {
                0 <= cur; cur < n;
                forall (k: int32) { 0 <= k and k < n implies 0 <= old(left[k]) and old(left[k]) < n };
                forall (k: int32) { 0 <= k and k < n implies 0 <= old(right[k]) and old(right[k]) < n };
                forall (k: int32) { 0 <= k and k < n implies old(left[k]) == at(after_mark, left[k]) };
                forall (k: int32) { 0 <= k and k < n implies old(right[k]) == at(after_mark, right[k]) };
            }
            have exists (path: Path) { walk(old(left), old(right), cur, path) == to } by {
                witness(path = Path::Left(rest));
                simp() using {
                    walk(old(left), old(right), cur, Path::Left(rest)) == walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest));
                    walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest)) == to;
                }
            }
            have left_result != 0 implies 0 <= to and to < n and at(after_mark, visited[to]) == 0 by { assumption(); }
            have 0 <= to and to < n and at(after_mark, visited[to]) == 0 by {
                extract(0 <= to and to < n and at(after_mark, visited[to]) == 0);
                assumption();
            }
            have old(visited[to]) == 0 by {
                if old(visited[to]) != 0 {
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and old(visited[k]) != 0 implies at(after_mark, visited[k]) != 0
                    }, to) using { 0 <= to; to < n; old(visited[to]) != 0; }
                    contradiction(at(after_mark, visited[to]) == 0);
                } else { simp(); }
            }
            step();
            simp();
        }
        else {}
    }
    observe(bounded_successors(left, right, n));
    have viewable(visited[0..n]) by { simp(); }
    apply(unmarked_nonnegative(visited, 0, n, n)) using {
        0 <= 0;
        0 <= n;
        n <= n;
        n <= 1073741823;
        viewable(visited[0..n]);
        0 <= n - 0;
        n - 0 <= 1073741823;
    }
    have unmarked(visited, 0, n) <= unmarked(at(after_mark, visited), 0, n) by {
        simp();
    }
    have unmarked(at(after_mark, visited), 0, n)
        == unmarked(at(before_mark, visited), 0, n) - 1 by {
        simp();
    }
    have unmarked(visited, 0, n) < old(unmarked(visited, 0, n)) by {
        arithmetic() using {
            unmarked(visited, 0, n) <= unmarked(at(after_mark, visited), 0, n);
            unmarked(at(after_mark, visited), 0, n)
                == unmarked(at(before_mark, visited), 0, n) - 1;
            unmarked(at(before_mark, visited), 0, n)
                == old(unmarked(visited, 0, n));
        }
    }
    have 0 <= right[cur] and right[cur] < n by {
        instantiate(forall (k: int32) {
            0 <= k and k < n implies 0 <= right[k] and right[k] < n
        }, cur) using { 0 <= cur; cur < n; }
        assumption();
    }
    mark before_right;
    have forall (k: int32) {
        0 <= k and k < n implies old(left[k]) == at(before_right, left[k])
    } by {
        intro(); intro();
        extract(0 <= k); extract(k < n);
        instantiate(forall (k: int32) {
            0 <= k and k < n implies old(left[k]) == at(after_mark, left[k])
        }, k) using { 0 <= k; k < n; }
        transport(old(left[k]) == at(after_mark, left[k]), old(left[k]) == at(before_right, left[k])) using {
            old(left[k]) == at(after_mark, left[k]);
            0 <= k; k < n;
            separate(memory(left[0..n]), memory(visited[0..n]));
        };
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < n implies old(right[k]) == at(before_right, right[k])
    } by {
        intro(); intro();
        extract(0 <= k); extract(k < n);
        instantiate(forall (k: int32) {
            0 <= k and k < n implies old(right[k]) == at(after_mark, right[k])
        }, k) using { 0 <= k; k < n; }
        transport(old(right[k]) == at(after_mark, right[k]), old(right[k]) == at(before_right, right[k])) using {
            old(right[k]) == at(after_mark, right[k]);
            0 <= k; k < n;
            separate(memory(right[0..n]), memory(visited[0..n]));
        };
        assumption();
    }

    have unmarked(at(before_right, visited), 0, n)
        <= old(unmarked(visited, 0, n)) by { simp(); }
    have forall (k: int32) {
        0 <= k and k < n and old(visited[k]) != 0 implies at(before_right, visited[k]) != 0
    } by { assumption(); }
    let right_result = step(dfs(left, right, visited, n, right[cur], to), {});
    have forall (k: int32) {
        0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
    } by { assumption(); }
    apply(marked_transitive(old(visited), at(before_right, visited), visited, n)) using {
        forall (k: int32) { 0 <= k and k < n and old(visited[k]) != 0 implies at(before_right, visited[k]) != 0 };
        forall (k: int32) { 0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0 };
    }

    have unmarked(visited, 0, n)
        <= unmarked(at(before_right, visited), 0, n) by { simp(); }
    have unmarked(visited, 0, n) <= old(unmarked(visited, 0, n)) by {
        arithmetic() using {
            unmarked(visited, 0, n)
                <= unmarked(at(before_right, visited), 0, n);
            unmarked(at(before_right, visited), 0, n)
                <= old(unmarked(visited, 0, n));
        }
    }
    if right_result != 0 {
        have right_result != 0 implies exists (path: Path) {
            walk(at(before_right, left), at(before_right, right), at(before_right, right[cur]), path) == to
        } by { assumption(); }
        have exists (path: Path) {
            walk(at(before_right, left), at(before_right, right), at(before_right, right[cur]), path) == to
        } by { simp(); }
        let (right_rest: Path) satisfy {
            walk(at(before_right, left), at(before_right, right), at(before_right, right[cur]), right_rest) == to
        };
        have walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest)) == to by {
            unfold(walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest)));
            assumption();
        }
        apply(walk_frame(old(left), old(right), at(before_right, left), at(before_right, right), n, cur, Path::Right(right_rest))) using {
            0 <= cur; cur < n;
            forall (k: int32) { 0 <= k and k < n implies 0 <= old(left[k]) and old(left[k]) < n };
            forall (k: int32) { 0 <= k and k < n implies 0 <= old(right[k]) and old(right[k]) < n };
            forall (k: int32) { 0 <= k and k < n implies old(left[k]) == at(before_right, left[k]) };
            forall (k: int32) { 0 <= k and k < n implies old(right[k]) == at(before_right, right[k]) };
        }
        have exists (path: Path) { walk(old(left), old(right), cur, path) == to } by {
            witness(path = Path::Right(right_rest));
            simp() using {
                walk(old(left), old(right), cur, Path::Right(right_rest)) == walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest));
                walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest)) == to;
            }
        }
        have right_result != 0 implies 0 <= to and to < n and at(before_right, visited[to]) == 0 by { assumption(); }
        have 0 <= to and to < n and at(before_right, visited[to]) == 0 by {
            extract(0 <= to and to < n and at(before_right, visited[to]) == 0);
            assumption();
        }
        have old(visited[to]) == 0 by {
            if old(visited[to]) != 0 {
                instantiate(forall (k: int32) {
                    0 <= k and k < n and old(visited[k]) != 0 implies at(before_right, visited[k]) != 0
                }, to) using { 0 <= to; to < n; old(visited[to]) != 0; }
                contradiction(at(before_right, visited[to]) == 0);
            } else { simp(); }
        }

        step();
        simp();
    } else {
        step();
        simp();
    }
}
```

```expect
pass
```
