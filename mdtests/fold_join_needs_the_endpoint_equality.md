# A fold does not join held ranges with a gap between them

The companion refusal to
[`fold_joins_ranges_abutting_by_proved_equality.md`](fold_joins_ranges_abutting_by_proved_equality.md).
Here the requirement says only that the live interval ends at or before the
free tail starts, `a.hi <= b.start`. The cells between them are owned by no
one in this proof, so `data[l..cap]` is not the union of what the proof
holds and the fold is refused. Looking endpoints up through equality premises
joins only ranges those premises make abut; it never bridges a gap.

```c filename=join.c
void join(int32* data, int32 cap) {
}
```

```click
resource suffix(data: int32*, cap: int32) {
    field start: int32;
    owns data[start..cap];
    fact 0 <= start;
    fact start <= cap;
}

resource piece(data: int32*) {
    field lo: int32;
    field hi: int32;
    owns data[lo..hi];
    fact 0 <= lo;
    fact lo < hi;
}

verifying "join.c";

void join(int32* data, int32 cap) {
    consumes a: piece(data);
    consumes b: suffix(data, cap);
    requires a.hi <= b.start;
    produces c: suffix(data, cap);
    ensures c.start == old(a.lo);
} by {
    let { lo: l, hi: h } = unfold(a);
    let { start: t } = unfold(b);
    have h <= cap by {
        simp() using {
            h <= t;
            t <= cap;
        }
    }
    have l < cap by {
        apply(int32_lt_le_transitive(l, h, cap)) using {
            l < h;
            h <= cap;
        }
    }
    have l <= cap by {
        apply(int32_lt_implies_le(l, cap)) using { l < cap; }
    }
    let c = fold(suffix(data, cap), { start: l });
    execute();
    simp();
}
```

```expect
fail: fold requires ownership of the complete instance body
```
