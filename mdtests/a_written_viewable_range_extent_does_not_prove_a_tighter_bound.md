# A written `viewable` range's extent does not prove a tighter bound

`requires viewable(a[0..n])` over `int32` gives `n <= 1073741823`, and no
more: `n == 1073741823` is a valid extent of `4294967292` bytes. Returning `n`
therefore does not establish `result <= 1073741822`. The true neighbour is
`mdtests/a_written_viewable_range_states_its_extent_in_the_signed_spelling.md`.

```c filename=a_written_viewable_range_extent_does_not_prove_a_tighter_bound.c
int32 count_viewable(int32 *a, int32 n) {
    return n;
}
```

```click
verifying "a_written_viewable_range_extent_does_not_prove_a_tighter_bound.c";

int32 count_viewable(int32 *a, int32 n) {
    requires viewable(a[0..n]);
    ensures result <= 1073741822 by auto;
}
```

```expect
fail: `ensures result <= 1073741822` failed
```
