# Joining the exits is not assuming the first conjunct's negation

This is the program of `mdtests/while_guard_unreadable_operand_rejected.md`
with the `views` clause that makes both operands readable, so the guard is
decided and both exits are certified rather than refused. The join must still
not prove `result == 0`: the loop exits with `a` nonzero whenever `p[0]` is
zero, and that path is one of the two the rule joined.

The exit states the disjunction `a == 0 or p[0] == 0`, never the first
disjunct on its own. Selecting a disjunct here is exactly the soundness hole
S1 closed, in the shape that only appears once a guard with several exits is
accepted at all.

```c filename=loop_conjunctive_guard_keeps_every_exit.c
int32 uprec_join(int32 a, int32 *p) {
    while (a != 0 && p[0] != 0) {
        a = 0;
    }
    return a;
}
```

```click
verifying "loop_conjunctive_guard_keeps_every_exit.c";

int32 uprec_join(int32 a, int32* p) {
    requires a >= 0;
    requires a <= 10;
    views p[0..1];
    ensures result == 0;
} by {
    loop {
        views p[0..1];
        invariant a >= 0;
        invariant a <= 10;
    }
    step();
    simp();
}
```

```expect
fail: unclosed goal: result == 0
```
