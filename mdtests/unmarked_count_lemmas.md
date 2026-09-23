# framing and point-updating a counting measure

`unmarked(v, lo, hi)` counts the cells of `v[lo..hi]` that hold zero. It is the
measure a pointer-chasing search that marks cells as it visits them descends
on, so the four facts such a proof needs are that the count is nonnegative
(`unmarked_nonnegative`), does not see cells outside its range
(`unmarked_frame`), cannot increase when marking only zero cells
(`unmarked_monotone`), and drops by exactly one when a previously unmarked cell
inside the range is marked (`unmarked_point_update`). All four are ordinary
`induct(hi)` proofs over the append-last-cell law
`unfold(unmarked(..)) using { lo <= hi - 1; hi - 1 < 2147483647; }` opens.
`unmarked_after_first_call_decreases` composes them into the ranking obligation
for a second recursive branch after the first branch has marked more cells.

Two things about the statements are forced rather than chosen.

The counted range ends at `hi`, the endpoint the induction descends on, but the
quantified premise that relates `a` and `b` is stated over a separate bound with
`hi <= m`. A premise that mentioned `hi` could not be supplied at `hi - 1`: the
induction hypothesis owes the premise the *kernel* gets by substituting
`hi := hi - 1`, and no surface spelling produces it, because writing `hi - 1`
inside a quantifier body lowers a definedness guard for the subtraction *into*
the body, in front of the written implication. `m` never moves, so the premise
at the smaller endpoint is the same proposition.

`unmarked_point_update` says "`b` is `a` with cell `j` marked" with two
half-range agreements, below `j` and above `j`, rather than one range with
`k != j`. The `k != j` spelling is provable at only one of the two places that
need it: `k < j` gives `k != j` through `int32_lt_implies_neq`, but the
symmetric `hi - 1 != j` from `j < hi - 1` needs a disequality symmetry Click
does not have. Split at `j`, each instantiation gets the orientation it can
prove, and the boundary case hands `unmarked_frame` its premise verbatim.

The ranges are `views` clauses. A stated range carries its extent half beside
its viewability half, so the proof never derives `0 <= n - lo` — but every
`apply` still owes both halves by name, which is the six `using` lines that
restate what the clause above them already said.

```click
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

theorem unmarked_monotone(a: int32[], b: int32[], lo: int32, n: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires n <= 1073741823;
    views a[lo..n];
    views b[lo..n];
    requires forall (k: int32) {
        lo <= k and k < n and a[k] != 0 implies b[k] != 0
    };
    ensures unmarked(b, lo, hi) <= unmarked(a, lo, hi) by {
        induct(hi) as ih;
        if hi <= lo {
            unfold(unmarked(a, lo, hi)) using { hi <= lo; }
            unfold(unmarked(b, lo, hi)) using { hi <= lo; }
            simp();
        } else {
            have 0 <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 < hi by { arithmetic() using { 0 <= lo; lo < hi; } }
            have lo <= hi - 1 by { arithmetic() using { 0 <= lo; lo < hi; } }
            have hi - 1 <= n by { arithmetic() using { 0 <= lo; lo < hi; hi <= n; } }
            have hi - 1 < n by { arithmetic() using { 0 <= lo; lo < hi; hi <= n; } }
            have hi - 1 < 2147483647 by { arithmetic() using { 0 <= lo; lo < hi; } }
            apply(ih(hi - 1)) using {
                0 <= hi - 1;
                hi - 1 < hi;
                0 <= lo;
                hi - 1 <= n;
                n <= 1073741823;
                viewable(a[lo..n]);
                viewable(b[lo..n]);
                forall (k: int32) {
                    lo <= k and k < n and a[k] != 0 implies b[k] != 0
                };
                0 <= n - lo;
                n - lo <= 1073741823;
            }
            have to_integer(if b[hi - 1] == 0 { 1 } else { 0 })
                <= to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) by {
                if a[hi - 1] == 0 {
                    have (if a[hi - 1] == 0 { 1 } else { 0 }) == 1 by {
                        normalize() using { a[hi - 1] == 0; }
                    }
                    have to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 1 by {
                        simp() using { (if a[hi - 1] == 0 { 1 } else { 0 }) == 1; };
                    }
                    if b[hi - 1] == 0 {
                        have (if b[hi - 1] == 0 { 1 } else { 0 }) == 1 by {
                            normalize() using { b[hi - 1] == 0; }
                        }
                        have to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 1 by {
                            simp() using { (if b[hi - 1] == 0 { 1 } else { 0 }) == 1; };
                        }
                        arithmetic() using {
                            to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 1;
                            to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 1;
                        }
                    } else {
                        have (if b[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                            normalize() using { b[hi - 1] != 0; }
                        }
                        have to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                            simp() using { (if b[hi - 1] == 0 { 1 } else { 0 }) == 0; };
                        }
                        arithmetic() using {
                            to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 1;
                            to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 0;
                        }
                    }
                } else {
                    have b[hi - 1] != 0 by {
                        instantiate(forall (k: int32) {
                            lo <= k and k < n and a[k] != 0 implies b[k] != 0
                        }, hi - 1) using {
                            lo <= hi - 1;
                            hi - 1 < n;
                            a[hi - 1] != 0;
                        }
                        assumption();
                    }
                    have (if a[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                        normalize() using { a[hi - 1] != 0; }
                    }
                    have (if b[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                        normalize() using { b[hi - 1] != 0; }
                    }
                    have to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                        simp() using { (if a[hi - 1] == 0 { 1 } else { 0 }) == 0; };
                    }
                    have to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                        simp() using { (if b[hi - 1] == 0 { 1 } else { 0 }) == 0; };
                    }
                    arithmetic() using {
                        to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 0;
                        to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 0;
                    }
                }
            }
            unfold(unmarked(a, lo, hi)) using {
                lo <= hi - 1;
                hi - 1 < 2147483647;
            }
            unfold(unmarked(b, lo, hi)) using {
                lo <= hi - 1;
                hi - 1 < 2147483647;
            }
            arithmetic() using {
                unmarked(b, lo, hi - 1) <= unmarked(a, lo, hi - 1);
                to_integer(if b[hi - 1] == 0 { 1 } else { 0 })
                    <= to_integer(if a[hi - 1] == 0 { 1 } else { 0 });
            }
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

theorem unmarked_after_first_call_decreases(
    entry: int32[],
    marked: int32[],
    after_left: int32[],
    lo: int32,
    n: int32,
    hi: int32
) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires n <= 1073741823;
    views entry[lo..n];
    views marked[lo..n];
    views after_left[lo..n];
    requires unmarked(marked, lo, hi) == unmarked(entry, lo, hi) - 1;
    requires forall (k: int32) {
        lo <= k and k < n and marked[k] != 0 implies after_left[k] != 0
    };
    ensures 0 <= unmarked(after_left, lo, hi) by {
        apply(unmarked_nonnegative(after_left, lo, n, hi)) using {
            0 <= lo;
            0 <= hi;
            hi <= n;
            n <= 1073741823;
            viewable(after_left[lo..n]);
            0 <= n - lo;
            n - lo <= 1073741823;
        }
        assumption();
    }
    ensures unmarked(after_left, lo, hi) < unmarked(entry, lo, hi) by {
        apply(unmarked_monotone(marked, after_left, lo, n, hi)) using {
            0 <= lo;
            0 <= hi;
            hi <= n;
            n <= 1073741823;
            viewable(marked[lo..n]);
            viewable(after_left[lo..n]);
            forall (k: int32) {
                lo <= k and k < n and marked[k] != 0 implies after_left[k] != 0
            };
            0 <= n - lo;
            n - lo <= 1073741823;
        }
        arithmetic() using {
            unmarked(marked, lo, hi) == unmarked(entry, lo, hi) - 1;
            unmarked(after_left, lo, hi) <= unmarked(marked, lo, hi);
        }
    }
}
```

```expect
pass
```
