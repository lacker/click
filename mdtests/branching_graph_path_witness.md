# Finite paths through a two-successor graph

`walk_frame` relates two graph snapshots by equality of their successor cells
inside `0..n`. Bounded successors keep every recursive step in that range.
Logical reads are total, so this pure theorem needs no memory permission or
implicit validity premises. Both directions of branching are checked.
`closed_marks_exclude_target` proves path exclusion by structural induction;
`exhausted_zero_entry` derives its closed marked set from the recursive failure
summary, unchanged target cell, and all-unmarked entry condition.

```click
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

theorem left_path(left: int32[], right: int32[], from: int32, rest: Path) {
    ensures walk(left, right, from, Path::Left(rest))
        == walk(left, right, left[from], rest) by {
        unfold(walk(left, right, from, Path::Left(rest)));
        normalize();
    }
}

theorem right_path(left: int32[], right: int32[], from: int32, rest: Path) {
    ensures walk(left, right, from, Path::Right(rest))
        == walk(left, right, right[from], rest) by {
        unfold(walk(left, right, from, Path::Right(rest)));
        normalize();
    }
}

theorem prepend_left(left: int32[], right: int32[], from: int32, to: int32) {
    requires exists (path: Path) {
        walk(left, right, left[from], path) == to
    };
    ensures exists (path: Path) { walk(left, right, from, path) == to } by {
        let (rest: Path) satisfy {
            walk(left, right, left[from], rest) == to
        };
        witness(path = Path::Left(rest));
        unfold(walk(left, right, from, Path::Left(rest)));
        assumption();
    }
}

theorem prepend_right(left: int32[], right: int32[], from: int32, to: int32) {
    requires exists (path: Path) {
        walk(left, right, right[from], path) == to
    };
    ensures exists (path: Path) { walk(left, right, from, path) == to } by {
        let (rest: Path) satisfy {
            walk(left, right, right[from], rest) == to
        };
        witness(path = Path::Right(rest));
        unfold(walk(left, right, from, Path::Right(rest)));
        assumption();
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
theorem closed_marks_exclude_target(left: int32[], right: int32[], v: int32[], n: int32, from: int32, to: int32, path: Path) {
    requires 0 <= from;
    requires from < n;
    requires v[from] != 0;
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n };
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= right[k] and right[k] < n };
    requires forall (k: int32) { 0 <= k and k < n and v[k] != 0 implies k != to and (v[left[k]] != 0 and v[right[k]] != 0) };
    ensures walk(left, right, from, path) != to by {
        induct(path) as ih {
            Path::Here => {
                instantiate(forall (k: int32) { 0 <= k and k < n and v[k] != 0 implies k != to and (v[left[k]] != 0 and v[right[k]] != 0) }, from) using { 0 <= from; from < n; v[from] != 0; }
                extract(from != to);
                unfold(walk(left, right, from, Path::Here));
                assumption();
            }
            Path::Left(rest) => {
                instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n }, from) using { 0 <= from; from < n; }
                extract(0 <= left[from]); extract(left[from] < n);
                instantiate(forall (k: int32) { 0 <= k and k < n and v[k] != 0 implies k != to and (v[left[k]] != 0 and v[right[k]] != 0) }, from) using { 0 <= from; from < n; v[from] != 0; }
                extract(v[left[from]] != 0);
                apply(ih(left, right, v, n, left[from], to, rest));
                unfold(walk(left, right, from, Path::Left(rest)));
                assumption();
            }
            Path::Right(rest) => {
                instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= right[k] and right[k] < n }, from) using { 0 <= from; from < n; }
                extract(0 <= right[from]); extract(right[from] < n);
                instantiate(forall (k: int32) { 0 <= k and k < n and v[k] != 0 implies k != to and (v[left[k]] != 0 and v[right[k]] != 0) }, from) using { 0 <= from; from < n; v[from] != 0; }
                extract(v[right[from]] != 0);
                apply(ih(left, right, v, n, right[from], to, rest));
                unfold(walk(left, right, from, Path::Right(rest)));
                assumption();
            }
        }
    }
}

theorem exhausted_zero_entry(left: int32[], right: int32[], before: int32[], after: int32[], n: int32, from: int32, to: int32) {
    requires 0 <= from;
    requires from < n;
    requires after[from] != 0;
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n };
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= right[k] and right[k] < n };
    requires forall (k: int32) { 0 <= k and k < n implies before[k] == 0 };
    requires forall (k: int32) { 0 <= k and k < n and before[k] == 0 and after[k] != 0 implies after[left[k]] != 0 and after[right[k]] != 0 };
    requires 0 <= to and to < n implies after[to] == before[to];
    ensures forall (path: Path) { walk(left, right, from, path) != to } by {
        have forall (k: int32) { 0 <= k and k < n and after[k] != 0 implies k != to and (after[left[k]] != 0 and after[right[k]] != 0) } by {
            intro(); intro();
            extract(0 <= k); extract(k < n); extract(after[k] != 0);
            instantiate(forall (k: int32) { 0 <= k and k < n implies before[k] == 0 }, k) using { 0 <= k; k < n; }
            instantiate(forall (k: int32) { 0 <= k and k < n and before[k] == 0 and after[k] != 0 implies after[left[k]] != 0 and after[right[k]] != 0 }, k) using { 0 <= k; k < n; before[k] == 0; after[k] != 0; }
            have k != to by {
                if k == to {
                    have 0 <= to by { simp(); }
                    have to < n by { simp(); }
                    have 0 <= to and to < n by { split(); }
                    extract(after[to] == before[to]);
                    have before[to] == 0 by {
                        instantiate(forall (k: int32) { 0 <= k and k < n implies before[k] == 0 }, to) using { 0 <= to; to < n; }
                        assumption();
                    }
                    have after[to] == 0 by { rewrite(after[to] == before[to]); assumption(); }
                    have after[k] == 0 by { rewrite(k == to); assumption(); }
                    contradiction(after[k] != 0);
                } else { assumption(); }
            }
            split();
        }
        intro();
        apply(closed_marks_exclude_target(left, right, after, n, from, to, path));
        assumption();
    }
}

```

```expect
pass
```
