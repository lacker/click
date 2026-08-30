# simple proof tactics

These proofs use only deterministic, bounded simple tactics. `assumption` reuses
an available semantic fact without deriving a new one, `normalize` computes a
proposition without consulting the proof context, and `rewrite` performs one
explicitly named equality substitution.

```c filename=simple_tactics.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "simple_tactics.c";

theorem exact_assumption(x: int32) {
    requires x >= 0;

    ensures x >= 0 by {
        assumption();
    }
}

theorem normalized_identity(x: int32) {
    ensures x + 1 == x + 1 by {
        normalize();
    }
}

theorem rewritten_identity(x: int32, y: int32) {
    requires x == y;

    ensures x + 1 == y + 1 by {
        rewrite(x == y);
        normalize();
    }
}

int32 identity(int32 x) {
    requires x == 7;
    ensures result == 7;
} by {
    execute();
    rewrite(x == 7);
    normalize();
}
```

```expect
pass
```
