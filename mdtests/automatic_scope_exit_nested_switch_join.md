# nested switch paths join after only one path constructs a local

The first inner case constructs an array and falls through to the shared
successor. The second case reaches that successor without constructing the
array. Both paths must clean up only the locals that actually exist.

```c filename=automatic_scope_exit_nested_switch_join.c
int32 nested_switch_join_preserves_scalar(int32 inner) {
    int32 result = 0;
    switch (0) {
        case 0:
            switch (inner) {
                case 0:
                    int32 a[1];
                    a[0] = 7;
                case 1:
                    result = 3;
                    break;
                default:
                    result = 3;
                    break;
            }
            break;
        default:
            break;
    }
    return result;
}
```

```click
verifying "automatic_scope_exit_nested_switch_join.c";

int32 nested_switch_join_preserves_scalar(int32 inner) {
    ensures result == 3 by auto;
}
```

```expect
pass
```
