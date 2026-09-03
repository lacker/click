# C `do ... while` loops

`do ... while` executes its body once before checking the condition. After
that first execution, `continue` goes to the condition and `break` exits the
loop.

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
        invariant i >= 0 and i < 2147483647;
    }
    simp();
}

```

```expect
pass
```
