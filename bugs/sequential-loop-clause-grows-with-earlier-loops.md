# A loop clause grows with the loops before it

A `loop { decreases ...; invariant ...; }` clause over one small loop costs
work that grows roughly quadratically with the number of earlier loops in the
function, so a function of N sequential loops is roughly cubic, and 64
four-iteration loops do not verify within the ten-minute containment bound.

Reproduced on master `e28770b20` with `scripts/step-scaling-hunt.py`:

```c
int32 caller(int32* p) {        /* owns p[0..4] */
    int32 i;
    i = 0;
    while (i < 4) { p[i] = 0; i = i + 1; }
    i = 0;
    while (i < 4) { p[i] = 1; i = i + 1; }
    ...                          /* N loops */
    return 0;
}
```

each proved by `step(); loop { decreases 4 - i; invariant i >= 0;
invariant i <= 4; }`.

```sh
python3 scripts/step-scaling-hunt.py loops --sizes 4,8,16,24
```

The last loop clause charges 4,460, 15,054, 58,704 and 132,304 units at
N = 4, 8, 16 and 24 (2.6 s for that one clause at N = 24). At N = 64 the 52nd
clause alone took 51 s and the run hit the ten-minute bound. Named
operations account for little of a late clause's work (its invariant closing
is about 5,000 units of 58,704 at N = 16), so the growth is in unattributed
work inside the clause.

Acceptance: a multi-size regression over `loops` shows each loop clause's
work and time constant in the number of earlier loops, up to logarithmic
factors; each loop's invariants and termination are still checked; no budget
or threshold is raised.
