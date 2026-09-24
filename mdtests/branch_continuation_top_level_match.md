# A proof `match` in a top-level `branch` continuation

The top-level sibling of `branch_continuation_nested_match.md`: the
`branch`'s `then` arm returns and its `else` arm runs the continuation, a
proof `match`, to function exit. The match used to leave the arm proof
attributed to its own tactic, so the branch's certificate checkpoint failed
with an internal "certificate checkpoint belongs to a different proof
context" error.

```c filename=branch_continuation_top_level_match.c
int32 f(int32* p, int32 x) {
    if (x <= 0) {
        return 0;
    }
    if (x < 5) {
        return 0;
    }
    return 1;
}
```

```click
verifying "branch_continuation_top_level_match.c";

spec enum T { A(int32) }

resource r(p: int32*) {
    field m: T;
    match m {
        T::A(v) => {
            owns p[0..1];
        },
    }
}

int32 f(int32* p, int32 x) {
    owns c: r(p);
    ensures result == 0 or result == 1;
} by {
    branch {
        then {
            step();
            simp();
        }
        else {}
    }
    match c.m {
        T::A(w) => {
            execute();
            simp();
        },
    }
}
```

```expect
pass
```
