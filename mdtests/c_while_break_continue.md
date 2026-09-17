# While-loop break and continue

C0 preserves the structured loop exits that are useful in ordinary search and
filter loops. `break` exits the innermost `while`; `continue` skips the rest of
the current body and rechecks the loop condition.

```c filename=stop_at_three.c
int32 stop_at_three() {
    int32 i = 0;
    while (i < 4) {
        if (i == 2) {
            break;
        }
        i++;
    }
    return i;
}
```

```c filename=sum_odd_positions.c
int32 sum_odd_positions() {
    int32 i = 0;
    int32 sum = 0;
    while (i < 4) {
        i++;
        if (i == 2) {
            continue;
        }
        sum += i;
    }
    return sum;
}
```

```click
verifying "stop_at_three.c";
verifying "sum_odd_positions.c";

int32 stop_at_three() {
    ensures result == 2 by auto;
}

int32 sum_odd_positions() {
    ensures result == 8 by auto;
}
```

```expect
pass
```
