# an inner switch break retires its automatic locals

The pointer survives the inner `switch`, but the array it designates does not.

```c filename=automatic_scope_exit_nested_switch_break.c
int32 nested_break_dangling() {
    int32* q;
    switch (0) {
        case 0:
            switch (0) {
                case 0:
                    int32 a[1];
                    a[0] = 5;
                    q = &a[0];
                    break;
                default:
                    break;
            }
            return q[0];
        default:
            return 0;
    }
}
```

```click
verifying "automatic_scope_exit_nested_switch_break.c";
int32 nested_break_dangling() { ensures 0 <= result; } by { execute(); simp(); }
```

```expect
fail: undefined behavior: invalid memory access
```
