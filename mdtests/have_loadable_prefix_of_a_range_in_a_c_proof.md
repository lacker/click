# `have loadable(...)` proves a prefix of a range in a C proof

`mdtests/have_loadable_prefix_of_a_range.md` narrows a stated loadable range in
a pure theorem, and `docs/concepts/loadability.md` promises the same narrowing
"in a pure theorem as well as in a C proof". The C half was refused, and for a
reason about term spelling rather than about the rule: a C contract almost
always states its range from `0`, and `loadable(a[0..n])` lowers its extent to
`n * 4`, whose element count is `n` with the `- 0` already folded away. The
narrowing rule read a count's endpoints off a subtraction, so a count with no
subtraction left in it looked like no range at all, and the one shape C
contracts write was the one shape the rule could not narrow. A range written
from `1` narrowed all along.

The endpoints of a count with nothing subtracted are `0` and the count, which is
the reading the extent's own validity check already gives such a count. With
both counts read that way, this proof asks the kernel exactly the question the
pure theorem asks, against the order facts the contract states, and the extent
requirement is untouched: the `requires` states the range, and a stated range
carries both halves of what it says, its bytes and its validity as a 32-bit
byte extent.

```c filename=have_loadable_prefix_of_a_range_in_a_c_proof.c
int32 probe(int32 a[], int32 n, int32 k) {
    return 0;
}
```

```click
verifying "have_loadable_prefix_of_a_range_in_a_c_proof.c";

int32 probe(int32 a[], int32 n, int32 k) {
    requires 0 <= k;
    requires k <= n;
    requires loadable(a[0..n]);
    ensures result == 0;
} by {
    step();
    have loadable(a[0..k]) by { simp(); }
    simp();
}
```

```expect
pass
```
