# A `branch` whose then arm returns while the else arm continues

The C `if` returns early on one side and falls through on the other. The
proof's `branch` spells only the returning arm; the else arm is empty and
the proof continues after the `branch`. The checked route runs that
continuation inside the continuing arm to function exit and joins the two
arms terminally, as `execute()` already does for such a C `if`.

```c filename=early_exit.c
int32 early_exit(int32 c) {
    int32 x;
    x = 0;
    if (c != 0) {
        return 1;
    }
    x = 2;
    return x;
}
```

```click
verifying "early_exit.c";

int32 early_exit(int32 c) {
    ensures result >= 0;
} by {
    step();
    step();
    branch {
        then {
            step();
            simp();
        }
        else {}
    }
    step();
    step();
    simp();
}
```

```expect
pass
```
