# Finite paths through a two-successor graph

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
    requires child: exists (path: Path) {
        walk(left, right, left[from], path) == to
    };
    ensures exists (path: Path) { walk(left, right, from, path) == to } by {
        choose(rest from requirement 0);
        witness(path = Path::Left(rest));
        unfold(walk(left, right, from, Path::Left(rest)));
        assumption();
    }
}

theorem prepend_right(left: int32[], right: int32[], from: int32, to: int32) {
    requires child: exists (path: Path) {
        walk(left, right, right[from], path) == to
    };
    ensures exists (path: Path) { walk(left, right, from, path) == to } by {
        choose(rest from requirement 0);
        witness(path = Path::Right(rest));
        unfold(walk(left, right, from, Path::Right(rest)));
        assumption();
    }
}
```

```expect
pass
```
