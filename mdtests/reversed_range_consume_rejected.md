# consuming a reversed range does not split ownership into overlapping parts

Consuming `p[lo..hi]` out of `owns p[0..10]` leaves the caller the parts on
either side of the consumed range. Those residues are disjoint only when the
consumed range is well formed: for `hi < lo` they would be `p[0..lo]` and
`p[hi..10]`, which overlap. Distinct owned facts are assumed separate, so an
overlapping pair would let a store through one survive as a stale load through
the other.

The call must fail unless `lo <= hi` is established, even though the reversed
range is trivially contained in the held range.

```c filename=reversed_range_consume_rejected.c
int32 borrow(int32* p, int32 lo, int32 hi) {
    return 0;
}

int32 reversed_range_consume_rejected(int32* p, int32 lo, int32 hi) {
    int32 first;
    int32 ignored;
    ignored = borrow(p, lo, hi);
    first = p[0];
    p[hi] = 7;
    return first;
}
```

```click
verifying "reversed_range_consume_rejected.c";

int32 borrow(int32* p, int32 lo, int32 hi) {
    consumes p[lo..hi];
}

int32 reversed_range_consume_rejected(int32* p, int32 lo, int32 hi) {
    requires 1 <= lo;
    requires lo <= 10;
    requires 0 <= hi;
    requires hi <= 9;
    consumes p[0..10];

    ensures result == p[0];
}
```

```expect
fail: missing resource fact
```
