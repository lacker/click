# A short-circuit loop guard leaves by one path per conjunct

`while (a != 0 && p[0] != 0)` has two ways out: `a` is zero, or `a` is nonzero
and `p[0]` is zero. S1 established that neither may be dropped — dropping the
second one assumes an exit state the C never reaches that way. The `loop`
tactic used to certify exactly one statement successor, so a guard with both
operands readable was refused with "requires exactly one statement successor,
got 2" even though every path was sound.

The loop rule now certifies all of them at once. Every guard-false path reaches
the same exit state, so the rule exports their join: the facts they all state,
which includes every invariant, followed by the disjunction of what each states
alone. `mdtests/loop_conjunctive_guard_exit_join.md` uses that disjunction and
`mdtests/loop_conjunctive_guard_keeps_every_exit.md` is the negative that shows
the first conjunct's negation alone is not assumed.

`for` lowers to the same `while`, so its guard joins the same way. A
disjunctive guard is the mirror image: `while (a != 0 || b != 0)` has two ways
*in* and one way out, and the single exit states both conjuncts false as
before.

An operand the function cannot read still refuses, in both spellings:
`mdtests/while_guard_unreadable_operand_rejected.md` and
`mdtests/for_guard_unreadable_operand_rejected.md` are the same programs
without the `views` clause.

```c filename=loop_conjunctive_guard_exits.c
int32 uprec_owned(int32 a, int32 *p) {
    while (a != 0 && p[0] != 0) {
        a = 0;
    }
    return a;
}

int32 ufor_owned(int32 a, int32 *p) {
    int32 i;
    for (i = a; i != 0 && p[0] != 0; i = i - 1) {
        i = 1;
    }
    return i;
}

int32 either(int32 a, int32 b) {
    while (a != 0 || b != 0) {
        a = 0;
        b = 0;
    }
    return a + b;
}
```

```click
verifying "loop_conjunctive_guard_exits.c";

int32 uprec_owned(int32 a, int32* p) {
    requires a >= 0;
    requires a <= 10;
    views p[0..1];
    ensures result >= 0;
    ensures result <= 10;
} by {
    loop {
        views p[0..1];
        invariant a >= 0;
        invariant a <= 10;
    }
    step();
    simp();
}

int32 ufor_owned(int32 a, int32* p) {
    requires a >= 0;
    requires a <= 10;
    views p[0..1];
    ensures result >= 0;
    ensures result <= 10;
} by {
    step();
    step();
    loop {
        views p[0..1];
        invariant i >= 0;
        invariant i <= 10;
    }
    step();
    simp();
}

int32 either(int32 a, int32 b) {
    requires a >= 0;
    requires a <= 1;
    requires b >= 0;
    requires b <= 1;
    ensures result == 0;
} by {
    loop {
        invariant a >= 0;
        invariant a <= 1;
        invariant b >= 0;
        invariant b <= 1;
    }
    step();
    simp();
}
```

```expect
pass
```
