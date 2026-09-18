# The entry join is a disjunction, not the first entry path

This is the program of
[`loop_disjunctive_guard_entry_join.md`](loop_disjunctive_guard_entry_join.md)
spelled `!= 0` instead of `> 0`, and it is the negative that keeps the entry
join honest. `while (a != 0 || b != 0)` is also entered on the path where `a`
is zero and `b` is not, so the body may not assume `a != 0`.

The entry paths export `a != 0 or b != 0` and nothing stronger. A proof that
names the first disjunct on its own is selecting a disjunct, which is the
entry-side shape of the soundness hole S1 closed on the exit side (see
[`loop_conjunctive_guard_keeps_every_exit.md`](loop_conjunctive_guard_keeps_every_exit.md)).
Citing `a != 0` as an exact premise is refused on the entry path that states
`a == 0`; the disjunction is the only thing the proof may split on.

```c filename=loop_disjunctive_guard_entry_join_is_a_disjunction.c
int32 enters_either_way(int32 a, int32 b) {
    while (a != 0 || b != 0) {
        a = 0;
        b = 0;
    }
    return a + b;
}
```

```click
verifying "loop_disjunctive_guard_entry_join_is_a_disjunction.c";

int32 enters_either_way(int32 a, int32 b) {
    requires a >= 0;
    requires a <= 1;
    requires b >= 0;
    requires b <= 1;
    ensures result == 0;
} by {
    loop {
        decreases a + b;
        invariant a >= 0;
        invariant a <= 1;
        invariant b >= 0;
        invariant b <= 1;
        preserve by {
            have 0 < a + b by {
                arithmetic() using { a != 0; a >= 0; b >= 0; a <= 1; b <= 1; }
            }
            step();
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: premise 0 is not exactly available
```
