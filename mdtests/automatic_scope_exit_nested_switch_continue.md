# a nested switch continue retires its automatic locals

The `continue` leaves both switches and reaches the enclosing loop, so the
inner array is gone before the pointer is read after the loop.

```c filename=automatic_scope_exit_nested_switch_continue.c
int32 nested_continue_dangling() {
    int32* q;
    int32 i = 0;
    while (i < 1) {
        i = i + 1;
        switch (0) {
            case 0:
                switch (0) {
                    case 0:
                        int32 a[1];
                        a[0] = 5;
                        q = &a[0];
                        continue;
                    default:
                        break;
                }
                break;
            default:
                break;
        }
    }
    return q[0];
}
```

```click
verifying "automatic_scope_exit_nested_switch_continue.c";
int32 nested_continue_dangling() { ensures 0 <= result; } by { execute(); simp(); }
```

```expect
fail: undefined behavior: invalid memory access
```
