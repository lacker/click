# loop invariant carries stdlib permutation

This checks the direct loop-invariant form of the standard-library
`permutation` predicate. Unfolding `permutation` reaches `count`, which uses
`.fold`; loop invariant spec lowering keeps that as pure Click core over
explicit current and entry memory snapshots.

The body writes only `i`, so the array argument `count` folds over names the
same snapshot at the back edge as at the iteration's start, and the
permutation invariant is preserved without a step of its own. The bundle the
closer sees is therefore the two `decreases` obligations; the invariant used
to need an `intro(); simp();` leaf beside them, when every statement renamed
that argument.

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
    ensures permutation_after_loop: permutation(p, old(p), 0, 3);
} by {
    step();
    step();
    loop {
        decreases 3 - i;
        invariant i >= 0 and i <= 3;
        invariant permutation(p, old(p), 0, 3);
        initialize by {
            unfold(permutation);
            simp();
        }
        preserve by {
            mark iteration;
            unfold(permutation);
            step();
            have i >= 0 and i <= 3 by simp;
            close_invariants by {
                both { arithmetic() using { at(iteration, i) < 3; at(iteration, i) >= 0; } }
                and { arithmetic() using { at(iteration, i) < 3; at(iteration, i) >= 0; } }
            }
        }
    }
    step();
    unfold(permutation);
    simp();
}
```

```expect
pass
```
