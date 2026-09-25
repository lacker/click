# A guarded call postcondition closes once its operands are bounded

`pick` states `st.live == old(st.live) + result`. Lowering that sum keeps its
no-overflow condition as a guard, so after the call the caller holds
`defined(old(st.live) + got) implies st.live == old(st.live) + got` rather
than the equality itself. The operands are bounded, `old(st.live)` by the
precondition and `got` by the finite value set `got == 0 or got == 1`, so the
guard holds; `simp` used to leave the consequent unused and fail on
`st.live == 1`.

The smart closer now selects the guarded equalities whose consequent shares
an operand with the goal from an index keyed by those operands, proves the
guard with an ordinary nested `simp` (overflow reasoning decides it from the
operands' bounds), extracts the consequent, and rewrites the goal with it.
Expansion renders each step: `have defined(1 + ..) by { .. }`,
`extract(st.live == old(st.live) + ..)`, and `rewrite(..)`
(`src/surface/tests/expansion_tests.rs`).

`restricted` lists the guarded fact in `simp() using { .. }` without its
guard: the guard is discharged the same way, from the listed premises when
they suffice, and the consequent replaces the implication in the list.

When the operands' bounds do not exclude overflow the consequent stays
unused: [`guarded_postcondition_unbounded_stays_guarded.md`](guarded_postcondition_unbounded_stays_guarded.md).

```c filename=guarded_postcondition_closes_after_call.c
struct box {
    int v;
};

int pick(struct box* b) {
    return 0;
}

int caller(struct box* b) {
    int got;
    got = pick(b);
    if (got == 0) {
        return 0;
    }
    return 1;
}

int restricted(struct box* b) {
    int got;
    got = pick(b);
    if (got == 0) {
        return 0;
    }
    return 1;
}
```

```click
resource counted(b: struct box*) {
    field live: int32;
    owns object(b);
    fact 0 <= live;
    fact live <= 100;
}

verifying "guarded_postcondition_closes_after_call.c";

int32 pick(struct box* b) {
    owns st: counted(b);
    ensures result == 0 or result == 1;
    ensures st.live == old(st.live) + result;
} by {
    let { live: n } = unfold(st);
    let st = fold(counted(b), { live: n });
    execute();
    simp();
}

int32 caller(struct box* b) {
    owns st: counted(b);
    requires st.live == 1;
    ensures result == 0 implies st.live == 1;
} by {
    step();
    step(pick(b), { st: st });
    execute();
    simp();
}

int32 restricted(struct box* b) {
    owns st: counted(b);
    requires st.live == 1;
    ensures result == 0 implies st.live == 1;
} by {
    step();
    mark m;
    step(pick(b), { st: st });
    branch {
        then {
            have got == 0 by {
                simp();
            }
            have at(m, st.live) == 1 by {
                simp();
            }
            have st.live == 1 by {
                simp() using {
                    defined(1 + got) implies st.live == at(m, st.live) + got;
                    got == 0;
                    at(m, st.live) == 1;
                }
            }
            step();
            simp();
        }
        else {}
    }
    step();
    simp();
}
```

```expect
pass
```
