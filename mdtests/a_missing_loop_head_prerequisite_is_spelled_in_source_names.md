# a missing loop-head prerequisite is spelled in source names

Assuming `viewable(a[0..i])` at the loop head also assumes its range is a valid
32-bit byte extent: `i` elements of four bytes fit, which is the unsigned bound
`i <= 1073741823`. Here `n` is unbounded above and the held range is the
constant `a[0..8]`, so nothing implies that bound and the loop is refused.
The refusal used to print the
kernel proposition itself,

```text
missing loop-head prerequisite: ConditionIs(Bitvector32SignedLessEqual(BitwiseXor(Constant(2147483648), Variable(Variable(1000000))), Constant(3221225471)), true)
```

the unsigned comparison in its sign-flipped signed encoding, over the kernel
variable the head minted for `i`. It now spells the comparison it means over
the local's name, and names the written invariant that owed it.

```c filename=a_missing_loop_head_prerequisite_is_spelled_in_source_names.c
int32 walk(int32 *a, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "a_missing_loop_head_prerequisite_is_spelled_in_source_names.c";

int32 walk(int32 *a, int32 n) {
    views a[0..8];
    requires 0 <= n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant viewable(a[0..i]);
    }
    step();
    simp();
}
```

```expect
fail: `walk.loop(0).preserve`: missing loop-head prerequisite: `i <= 1073741823 (unsigned)`, which invariant `viewable(a[0..i])` needs
```
