# loop invariant cannot yet carry stdlib permutation

This captures the current limitation for the direct loop-invariant form of the
standard-library `permutation` predicate. Unfolding `permutation` reaches
`count`, which uses `.fold`; loop invariant C lowering cannot yet represent pure
Click fold values over the current loop memory.

```c filename=loop_stdlib_permutation_invariant.c
int32 loop_stdlib_permutation_invariant(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_stdlib_permutation_invariant.c";

int32 loop_stdlib_permutation_invariant(int32 p[3]) {
    requires valid_range(p[0..3]);
    loop 0 {
        invariant i >= 0 and i <= 3 by auto;
        invariant permutation(p, old(p), 0, 3) by {
            unfold(permutation);
        }
        immutable by frame;
    }
    ensures permutation_after_loop: permutation(p, old(p), 0, 3) by {
        symbolic_execute();
        loop_vc(loop 0);
        frame(loop 0);
        simp();
        close();
    }
}
```

```expect
fail: `fold` expressions are not supported in loop invariant C lowering yet
```
