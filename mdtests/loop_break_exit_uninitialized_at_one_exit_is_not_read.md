# A local only some exits initialized cannot be read after the loop

`late` leaves its loop before assigning `seen` on one path and after on the
other. The join does not invent a value for the first path: where the exits
disagree on whether a local is initialized, the successor keeps the local's
slot and type and leaves it uninitialized. Returning `seen` after the loop is
then a read of uninitialized storage, and it is refused.

```c filename=late.c
int32 late(int32 flag) {
    int32 seen;
    while (true) {
        if (flag == 0) {
            break;
        }
        seen = 1;
        break;
    }
    return seen;
}
```

```click
verifying "late.c";

int32 late(int32 flag) {
    ensures result == 1;
} by {
    step();
    loop {
        decreases 0;

        maintain by {
            if flag == 0 {
                step();
                step();
            } else {
                step();
                step();
                step();
                step();
            }
        }
    }
    step();
    close();
}
```

```expect
fail: read of uninitialized storage
```
