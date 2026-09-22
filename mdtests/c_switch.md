# C `switch` cases and fallthrough

C0 keeps switch cases in source order. Dispatch enters the first matching
case, then continues through later cases until a `break` or the end of the
switch.

```c filename=switch_break.c
int32 switch_break(int32 kind) {
    int32 result = 0;
    switch (kind) {
        case 0:
            result = 10;
            break;
        case 1:
            result = 20;
            break;
        default:
            result = 30;
            break;
    }
    return result;
}
```

```c filename=switch_fallthrough.c
int32 switch_fallthrough(int32 kind) {
    int32 result = 0;
    switch (kind) {
        case 0:
            result = result + 1;
        case 1:
            result = result + 2;
            break;
        default:
            result = 9;
            break;
    }
    return result;
}
```

```c filename=switch_loop_control.c
int32 switch_loop_control() {
    int32 i = 0;
    while (i < 3) {
        switch (i) {
            case 0:
                i++;
                continue;
            default:
                break;
        }
        i++;
    }
    return i;
}
```

```c filename=switch_constant_labels.c
int32 switch_constant_labels(int32 kind) {
    int32 result = 0;
    switch (kind) {
        case 1 + 1:
            result = 10;
        case 1 + 2:
            result = result + 2;
            break;
        case 1 << 2:
            result = 40;
            break;
        default:
            result = 50;
            break;
    }
    return result;
}
```

```click
verifying "switch_break.c";
verifying "switch_fallthrough.c";
verifying "switch_loop_control.c";
verifying "switch_constant_labels.c";

int32 switch_break(int32 kind) {
    ensures result == 10 or result == 20 or result == 30 by auto;
}

int32 switch_fallthrough(int32 kind) {
    ensures result == 3 or result == 2 or result == 9 by auto;
}

int32 switch_loop_control() {
    ensures result == 3 by auto;
}

int32 switch_constant_labels(int32 kind) {
    ensures result == 12 or result == 2 or result == 40 or result == 50 by auto;
}
```

```expect
pass
```
