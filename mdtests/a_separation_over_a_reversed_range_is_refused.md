# A separation over a reversed range is refused

Naming a range in a contract says the same thing in every clause that can
name one: that `s..t` is a valid 32-bit byte extent. `owns a[s..t]` and
`viewable(a[s..t])` have carried that meaning both ways since a stated range
began carrying its byte extent. `separate(memory(a[s..t]), …)` did not, and
that made it the one clause where a range running backwards was accepted.

The endpoints here are pinned to `s = i32::MAX` and `t = -i32::MAX`. Their
*wrapping* difference is a tidy `2`, which is why the extent arithmetic alone
raises no objection — read as a residue the range looks like two elements.
Their true difference is `2 - 2^32`: the range's end is nearly the whole index
space before its start, so it denotes no bytes at all, and relating it to
another range states nothing. A separation clause is refused when the
surrounding facts already decide that, exactly as an `owns` clause over the
same endpoints is.

```c filename=a_separation_over_a_reversed_range_is_refused.c
int32 separate_over_reversed_range(int32 a[], int32 b[], int32 s, int32 t) {
    return b[0];
}
```

```click
verifying "a_separation_over_a_reversed_range_is_refused.c";

int32 separate_over_reversed_range(int32 a[], int32 b[], int32 s, int32 t) {
    requires s == 2147483647;
    requires t == -2147483647;
    requires separate(memory(a[s..t]), memory(b[0..1]));
    owns b[0..1];

    ensures result == b[0] by auto;
}
```

```expect
fail: it relates a memory range this context already proves is not a byte extent
```
