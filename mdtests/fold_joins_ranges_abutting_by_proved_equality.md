# A fold joins two held ranges that abut by a proved endpoint equality

`join` holds `piece(data)`, a live interval `[lo, hi)`, and `suffix(data,
cap)`, the free tail `[start, cap)`, and its requirement says the interval
ends where the tail starts. After unfolding both, the proof holds
`data[l..h]` and `data[t..cap]` together with the premise `h == t`. Folding
`suffix` at `l` asks for `data[l..cap]`, which is exactly those two ranges
joined.

Two held ranges merge when one's end is the other's start, as written or by
a proved equality. The merge rule has always accepted a proved equality; the
normalizer now also looks a range's endpoints up under the spellings the
premises make equal to them, so it offers the two pieces to each other
instead of only ranges whose endpoints are spelled identically. This is the
join `examples/arena`'s prefix `arena_free` needs when it returns the freed
region `[start, end)` to the free suffix `[prefix, capacity)` under
`end == prefix`. The companion refusal is
[`fold_join_needs_the_endpoint_equality.md`](fold_join_needs_the_endpoint_equality.md).

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
    requires a.hi == b.start;
    produces c: suffix(data, cap);
    ensures c.start == old(a.lo);
} by {
    let { lo: l, hi: h } = unfold(a);
    let { start: t } = unfold(b);
    have h == t by {
        assumption();
    }
    have h <= cap by {
        simp() using {
            h == t;
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
pass
```
