# A C proof applies a `viewable`-premise theorem with `using`

`mdtests/sweep_maintains_a_zero_unmarked_count.md` applies a theorem with
`viewable` premises from a C proof, and states every extent bound the
application owes as its own `using` entry. Naming the range and then restating
the bound the range already carries was not a style choice: an `apply … using`
list that named only the range was refused with

```text
theorem `...` requirement 1 `(n >= 0 && viewable(v[0..n]))` states a memory
range, so applying it needs that range to be a valid 32-bit byte extent here:
`n <= 1073741823 is true` is not an available fact
```

although the contract states exactly that bound.

Citing a stated range cites what the range says. `viewable(p[a..b])` means both
that `a..b` is a valid 32-bit byte extent and that those bytes are viewable, so
a `using` list that names the range has named both halves. `transport … using`
already reads a cited range that way; `apply … using` now does too. The
relaxation is one-sided: a guard joins the evidence set only where it is
already available at this point, in whichever spelling is available — the
endpoint form of the `fits` bound is an unsigned comparison the surface cannot
write at all.

```c filename=c_proof_applies_a_loadable_premise_theorem_with_using.c
int32 probe(int32 a[], int32 n) {
    return 0;
}
```

```click
verifying "c_proof_applies_a_loadable_premise_theorem_with_using.c";

theorem viewable_range_is_nonnegative(v: int32[], n: int32) {
    requires n >= 0 and viewable(v[0..n]);
    ensures 0 <= n by { simp(); }
}

int32 probe(int32 a[], int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    requires viewable(a[0..n]);
    ensures result == 0;
} by {
    step();
    have n >= 0 by { simp(); }
    have viewable(a[0..n]) by { simp(); }
    have n >= 0 and viewable(a[0..n]) by { split(); }
    apply(viewable_range_is_nonnegative(a, n)) using {
        n >= 0 and viewable(a[0..n]);
    }
    simp();
}
```

```expect
pass
```
