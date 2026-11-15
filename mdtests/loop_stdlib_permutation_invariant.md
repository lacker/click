# loop invariant carries stdlib permutation

This checks the direct loop-invariant form of the standard-library
`permutation` predicate. Unfolding `permutation` reaches `count`, which uses
`.fold`; loop invariant spec lowering keeps that as pure Click core over
explicit current and entry memory states.

The body writes only `i`, so the array argument `count` folds over names the
same state at the back edge as at the iteration's start, and the
permutation invariant is preserved without a step of its own. The bundle the
closer sees is therefore the two `decreases` obligations; the invariant used
to need an `intro(); solve();` leaf beside them, when every statement renamed
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
import click::permutation;

verifying "loop_stdlib_permutation_invariant.c";

int32 loop_stdlib_permutation_invariant(int32 p[3]) {
    requires viewable(p[0..3]);
    ensures permutation_after_loop: permutation::permutation(p, old(p), 0, 3);
} by {
    step();
    step();
    loop {
        decreases 3 - i;
        invariant i >= 0 and i <= 3;
        invariant permutation::permutation(p, old(p), 0, 3);
        initialize by {
            unfold(permutation::permutation);
            solve();
        }
        preserve by {
            mark iteration;
            unfold(permutation::permutation);
            step();
            have i >= 0 and i <= 3;
        }
    }
    step();
    unfold(permutation::permutation);
    solve();
}
```

```expect
pass
```
