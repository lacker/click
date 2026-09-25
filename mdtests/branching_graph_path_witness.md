# Finite paths through a two-successor graph

`walk_frame` relates two graph snapshots by equality of their successor cells
inside `0..n`. Bounded successors keep every recursive step in that range.
Logical reads are total, so this pure theorem needs no memory permission or
implicit validity premises. Both directions of branching are checked.

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
```

```expect
pass
```
