# A matched arm can state int32 arithmetic over its payload with `defined`

A resource body fact that computes over a constructor payload, such as
`x + 2 <= 10`, can only be unfolded when the arithmetic is known defined.
Stating `defined(x + 2)` as an earlier body fact supplies that evidence, so
the later fact lowers on a single clean path.

```c filename=payload_arith_fact_defined.c
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
            fact defined(x + 2);
            fact x + 2 <= 10;
        },
    }
}

verifying "payload_arith_fact_defined.c";

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
pass
```
