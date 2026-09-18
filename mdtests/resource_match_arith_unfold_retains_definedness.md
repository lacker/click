# Unfolding a matched arm retains its arithmetic definedness conditions

A resource body fact that computes over a constructor payload, such as
`x + 2 <= 10`, exposes both the comparison and the condition that the
arithmetic is defined. The unfold succeeds without a preceding
`defined(...)` fact, and the retained definedness is available to the rest
of the proof.

```c filename=payload_arith_unfold_retains_definedness.c
int32 keep(int32* p) {
    return p[0];
}
```

```click
spec enum Tag { T(int32) }

resource box(p: int32*) {
    field tag: Tag;
    match tag {
        Tag::T(x) => {
            owns p[0..1];
            fact x + 2 <= 10;
        },
    }
}

verifying "payload_arith_unfold_retains_definedness.c";

int32 keep(int32* p) {
    owns b: box(p);
    ensures result == p[0];
} by {
    match b.tag {
        Tag::T(x) => {
            unfold(b);
            have defined(x + 2) by {
                assumption();
            }
            execute();
            let b = fold(box(p), { tag: Tag::T(x) });
            simp();
        },
    }
}
```

```expect
pass
```
