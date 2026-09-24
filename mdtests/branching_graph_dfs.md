# A cyclic, two-successor graph search

The C is the graph search from `design/dfs-gaps/branching_graph_dfs.md`, unchanged.
Both successor arrays are bounded and read-only; `visited` is mutable. The
number of unmarked cells ranks both recursive calls, including the right call
after the left call may have marked additional nodes.

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
} by {
    branch {
        then { step(); simp(); }
        else {}
    }
    branch {
        then { step(); simp(); }
        else {}
    }
    mark before_mark;
    step();
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
    step();
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
        then { step(); simp(); }
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
    have unmarked(at(before_right, visited), 0, n)
        <= old(unmarked(visited, 0, n)) by { simp(); }
    step();
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
    step();
    simp();
}
```

```expect
pass
```
