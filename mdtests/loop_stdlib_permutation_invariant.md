# loop invariant carries stdlib permutation

This checks the direct loop-invariant form of the standard-library
`permutation` predicate. Unfolding `permutation` reaches `count`, which uses
`.fold`; loop invariant spec lowering keeps that as pure Click core over
explicit current and entry memory snapshots.

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
    requires loadable(p[0..3]);
    for loop(0) {
        invariant i >= 0 and i <= 3;
        invariant permutation(p, old(p), 0, 3);
        initialize by {
            unfold(permutation);
        }
        preserve by {
            unfold(permutation);
        }
        immutable by frame;
    }
    ensures permutation_after_loop: permutation(p, old(p), 0, 3) by {
        execute_rest();
        loop_vc(loop(0));
        frame(loop(0));
        unfold(permutation);
        simp();
    }
}
```

```expect
pass
```
