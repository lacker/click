# C `do ... while` loops

`do ... while` executes its body once before checking the condition. After
that first execution, `continue` goes to the condition and `break` exits the
loop.

The guard is read after the body, so the state a body path ends in *is* the
loop's guard-false exit; there is no separate exit at the head. `do_while_invariant`
is where that shows: the loop head is an arbitrary visit, so `i` there is
abstract and only the invariant says anything about it, and the postcondition
`result == 1` is read off the invariant at the value the body's increment
produced. The invariant is written `i + 1 == 1` rather than `i == 0` because a
proof after the loop reads the exported invariant facts in the terms the head
stated them.

The first three proofs carry no loop annotation, so certification executes
their constant-bound loops to the exit and that execution is their termination
evidence. `do_while_invariant` summarizes its loop instead, so it declares
`decreases i;`; the guard `0` means the back edge is never reached, and only
the measure's nonnegativity is proved.

```c filename=do_while_count.c
int32 do_while_count() {
    int32 i = 0;
    do {
        i++;
    } while (i < 3);
    return i;
}
```

```c filename=do_while_runs_once.c
int32 do_while_runs_once() {
    int32 i = 0;
    do {
        i++;
    } while (0);
    return i;
}
```

```c filename=do_while_control.c
int32 do_while_control() {
    int32 i = 0;
    int32 sum = 0;
    do {
        i++;
        if (i == 2) {
            continue;
        }
        if (i == 4) {
            break;
        }
        sum += i;
    } while (i < 6);
    return sum;
}
```

```c filename=do_while_invariant.c
int32 do_while_invariant(int32 i) {
    do {
        i++;
    } while (0);
    return i;
}
```

```click
verifying "do_while_count.c";
verifying "do_while_runs_once.c";
verifying "do_while_control.c";
verifying "do_while_invariant.c";

int32 do_while_count() {
    ensures result == 3 by auto;
}

int32 do_while_runs_once() {
    ensures result == 1 by auto;
}

int32 do_while_control() {
    ensures result == 4 by auto;
}

int32 do_while_invariant(int32 i) {
    requires i == 0;
    ensures result == 1;
} by {
    loop {
        decreases i;
        invariant i + 1 == 1;
    }
    step();
    simp();
}

```

```expect
pass
```
