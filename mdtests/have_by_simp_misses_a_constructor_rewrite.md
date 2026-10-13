# `simp` does not rewrite a constructor term back to its model

The same goal as `auto_rewrites_a_constructor_term_to_its_model.md`, proved
with `simp`, which does not rewrite the goal by the arm's equality here.

```c filename=have_by_simp_misses_a_constructor_rewrite.c
void touch(int32 n) {
}
```

```click
verifying "have_by_simp_misses_a_constructor_rewrite.c";

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
            have black(Walk::At(wd, rest)) == 1 by simp;
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
fail: could not establish `black(Walk::At(wd, rest)) == 1`
```
