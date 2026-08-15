# conditional call ensure discharged by explicit modus ponens

A callee's conditional ensure reaches the caller as an implication fact.
Once the caller's branch establishes the antecedent, `simp() using` with
exactly the antecedent and the implication must prove the consequent, and
its certificate must lower to the explicit bounded rule (`extract` of the
discharged consequent, then `assumption`) rather than reporting a missing
simple proof rule.

```c filename=set_five.c
int32 set_five(int32* cell) {
    cell[0] = 5;
    return 1;
}
```

```c filename=use_five.c
int32 use_five(int32* cell) {
    int32 flag;
    flag = set_five(cell);
    if (flag == 1) {
        return cell[0];
    }
    return 0;
}
```

```click
verifying "set_five.c";
verifying "use_five.c";

int32 set_five(int32* cell) {
    owns cell[0..1];
    mutable cell[0..1];
    ensures result == 0 or result == 1;
    ensures result == 1 implies cell[0] == 5;
} by auto;

int32 use_five(int32* cell) {
    owns cell[0..1];
    mutable cell[0..1];
} by {
    step();
    step();
    if c(flag) == 1 {
        have cell[0] == 5 by {
            simp() using {
                c(flag) == 1;
                c(flag) == 1 implies cell[0] == 5;
            }
        }
        execute();
        frame() using {
        }
        assumption();
    } else {
        execute();
        frame() using {
        }
        assumption();
    }
}
```

```expect
pass
```
