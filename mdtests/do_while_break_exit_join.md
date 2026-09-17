# A `do ... while` exports the exit its guard decides

A `do ... while` reads its guard after the body, so the state a body path ends
in *is* the loop's guard-false exit — there is no exit at the head to fall back
on. When the surface proves preservation itself, that state used to be recorded
only if the body failed to close the back edge, which a scalar body never does,
so the loop exported no exit at all and every claim after it held vacuously:
[`do_while_break_exit_vacuous_rejected.md`](do_while_break_exit_vacuous_rejected.md)
and
[`do_while_no_exit_state_rejected.md`](do_while_no_exit_state_rejected.md) are
the two reductions that used to verify and now fail.

A body path's end state is now always one of the loop's exits, and it joins the
`break` exits into the single successor on the same terms as a `while` loop's
guard-false exit. `do_break_flag` has both: the `break` leaves with `i == 3`,
the guard-false exit leaves with `i == 0`, and the post-loop claim reads their
disjunction.

```c filename=do_break_flag.c
int32 do_break_flag(int32 flag) {
    int32 i = 0;
    do {
        if (flag == 3) {
            i = 3;
            break;
        }
        i = 0;
    } while (i > 0);
    return i;
}
```

```click
verifying "do_break_flag.c";

int32 do_break_flag(int32 flag) {
    ensures result == 3 or result == 0;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
    }
    step();
    simp();
}
```

```termination
pending: unranked loop
```

```expect
pass
```
