# `auto` rewrites a constructor term back to the model a match arm names

The arm knows `c.model == Walk::At(wd, rest)` and the requirement states
`black(c.model) == 1`. `simp` misses the goal, which names the constructor term
(`have_by_simp_misses_a_constructor_rewrite.md`). `auto` searches short chains
of rewrites by the equalities connected to the goal, in either direction, and
closes the rewritten goal by `assumption`. Each rewrite is a checked step, and
`click expand` writes the chain it found as `rewrite` steps.

```c filename=auto_rewrites_a_constructor_term_to_its_model.c
void touch(int32 n) {
}
```

```click
verifying "auto_rewrites_a_constructor_term_to_its_model.c";

spec enum Walk { At(Integer, Walk), Done }

function black(w: Walk) -> int32 decreases w {
    match w { Walk::At(wd, rest) => black(rest), Walk::Done => 1 }
}

resource token(k: int32) {
    field model: Walk;
}

void touch(int32 n) {
    owns c: token(n);
    requires black(c.model) == 1;
    ensures 1 == 1;
} by {
    match c.model {
        Walk::At(wd, rest) => {
            have black(Walk::At(wd, rest)) == 1 by auto;
            step();
            step();
            simp();
        },
        Walk::Done => {
            step();
            step();
            simp();
        },
    }
}
```

```expect
pass
```
