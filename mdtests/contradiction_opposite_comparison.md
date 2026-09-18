# a contradiction between a comparison and its arithmetic negation

`contradiction(p)` closes a branch that holds both `p` and its negation.
`x < 0` and `x >= 0` are that pair, but they are two different lowered
conditions rather than one condition at both polarities, so the negation is
recognized through the same bounded list of equivalent spellings a disjunct
arm uses. Nothing is searched: the list is fixed and each spelling is looked
up exactly.

```c filename=contradiction_opposite_comparison.c
int32 nonnegative_identity(int32 x) {
    return x;
}
```

```click
verifying "contradiction_opposite_comparison.c";

int32 nonnegative_identity(int32 x) {
    requires x >= 0;
    ensures result == x;
} by {
    have x < 0 implies x == 7 by {
        intro();
        contradiction(x < 0);
    }
    step();
    simp();
}
```

```expect
pass
```
