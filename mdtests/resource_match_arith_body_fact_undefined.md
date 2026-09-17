# Unfolding arithmetic over a payload without `defined` reports possible undefined behavior

A resource body fact that computes over a constructor payload, such as
`x + 2 <= 10`, might be undefined behavior when nothing establishes that
the arithmetic is defined. Unfolding it reports that directly instead of a
generic conditional-proof failure.

```c filename=payload_arith_fact_undefined.c
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

verifying "payload_arith_fact_undefined.c";

int32 keep(int32* p) {
    owns b: box(p);
    ensures result == p[0];
} by {
    match b.tag {
        Tag::T(x) => {
            unfold(b);
            execute();
            let b = fold(box(p), { tag: Tag::T(x) });
            simp();
        },
    }
}
```

```expect
fail: instance body fact might be undefined behavior: addition overflow is not ruled out
```
