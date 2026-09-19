# a contract cannot state a range whose extent wraps

A stated range carries its byte-count guards as facts, so the one thing that
must not be possible is stating a range whose guards are false: the clause
would hand the proof a valid-extent fact about a range that has none, and
`mdtests/wrapped_viewable_extent_is_not_a_cell.md` is what that buys.

Stating one is refused where the clause is prepared, by the same shared
definition the guards come from. `n == 1073741824` makes the element count of
`p[0..n]` decidably too wide for a four-byte extent, so `views p[0..n]` never
becomes an assumption at all — the refusal is about the clause, not about the
proof that would have used it.

The same check covers `owns` and aggregate ranges, which carry the guards too.

```c filename=wrapped_view.c
int32 wrapped_view(int32* p, int32 n) {
    return p[0];
}
```

```click
verifying "wrapped_view.c";

int32 wrapped_view(int32* p, int32 n) {
    requires n == 1073741824;
    requires 0 < n;
    views p[0..n];
    ensures result == p[0] by auto;
}
```

```expect
fail: memory range requires the verifier to have assumed a condition fact that cannot hold
```
