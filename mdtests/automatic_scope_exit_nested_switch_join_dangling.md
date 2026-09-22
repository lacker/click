# a joined nested-switch path cannot retain a case-local pointer

The fallback array remains alive, but the pointer is redirected to the inner
array only on the case that constructs it. After the nested switch joins,
that case-local array has been retired before the pointer is read.

```c filename=automatic_scope_exit_nested_switch_join_dangling.c
int32 nested_switch_join_dangling(int32 inner) {
    int32 fallback[1];
    fallback[0] = 3;
    int32* q = &fallback[0];
    switch (0) {
        case 0:
            switch (inner) {
                case 0:
                    int32 a[1];
                    a[0] = 7;
                    q = &a[0];
                case 1:
                    break;
                default:
                    break;
            }
            break;
        default:
            return 0;
    }
    return q[0];
}
```

```click
verifying "automatic_scope_exit_nested_switch_join_dangling.c";
int32 nested_switch_join_dangling(int32 inner) { ensures 0 <= result; } by { execute(); simp(); }
```

```expect
fail: undefined behavior: invalid memory access
```
