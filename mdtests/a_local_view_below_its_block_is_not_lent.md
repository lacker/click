# a view below a local's block is not storage the caller can lend

A caller lends a view over its own stack object without a resource clause,
because the object is its own. What it may lend is the storage the block
actually has, and `local_view_range_within_block` is the check.

It read both endpoints through `Bitvector32Term::as_const`, which answers
`u32`, and then took `end <= start` as "an empty range names no storage". A
start of `-1` arrives there as `4294967295`, so every range that begins below
its block took that exit and `memory.access_in_bounds` never ran — the exact
opposite of what the check asks.

    int32 first(int32* values, int32 s, int32 e) {
        return values[0];
    }                                    //  views values[s..e]

    int32 lends_below_its_local() {
        int32 pair[2];
        pair[0] = 1;
        pair[1] = 2;
        return first(pair, -1, 3);       //  lends pair[-1..3]
    }

`pair` is two elements. The call lent four, one of them below the object and
one past it, and it verified. The contained range is the control: the same
call at `0, 3` is refused with `missing resource fact`, so a *superset* of a
refused range was being admitted.

Both endpoints are now read signed, which is the reading
`memory_range_byte_count` already scales, and the byte count is computed in
`i64` before it is narrowed. `lends_its_whole_local` beside it is the
positive: the same call over the two elements the caller has.

```c filename=a_local_view_below_its_block_is_not_lent.c
int32 first(int32* values, int32 s, int32 e) {
    return values[0];
}

int32 lends_its_whole_local() {
    int32 pair[2];
    pair[0] = 1;
    pair[1] = 2;
    return first(pair, 0, 2);
}

int32 lends_below_its_local() {
    int32 pair[2];
    pair[0] = 1;
    pair[1] = 2;
    return first(pair, -1, 3);
}
```

```click
verifying "a_local_view_below_its_block_is_not_lent.c";

int32 first(int32* values, int32 s, int32 e) {
    requires s <= 0;
    requires 0 < e;
    views values[s..e];
    ensures result == values[0];
}

int32 lends_its_whole_local() {
    ensures result == 1;
}

int32 lends_below_its_local() {
    ensures result == 1;
}
```

```expect
fail: missing resource fact `views local:pair@0[-1..3]`
```
