# the supported `do ... while` `continue` shapes still lower

The companion to `do_while_switch_continue_rejected.md`. Only the combination
of a `switch`-enclosed `continue` and a condition containing a call is
rejected; each half on its own keeps working, and both results match what a C
compiler computes.

```c filename=do_while_continue_shapes.c
int32 stop_now() {
    return 0;
}

int32 switch_continue_plain_condition() {
    int32 count = 0;
    int32 tail = 0;
    do {
        count++;
        switch (count) {
            case 1:
                continue;
            default:
                break;
        }
        tail++;
    } while (count < 3);
    return tail;
}

int32 call_condition_without_switch() {
    int32 count = 0;
    int32 tail = 0;
    do {
        count++;
        if (count == 1) {
            continue;
        }
        tail++;
    } while (stop_now());
    return tail;
}
```

```click
verifying "do_while_continue_shapes.c";

int32 stop_now() {
    ensures result == 0 by auto;
}

int32 switch_continue_plain_condition() {
    ensures result == 2 by auto;
}

int32 call_condition_without_switch() {
    ensures result == 0 by auto;
}
```

```expect
pass
```
