# nested switch fallthrough and return clean up automatic locals

An inner switch keeps its local alive across fallthrough, and a scalar return
can read that local before both the inner and outer switch scopes are retired.

```c filename=automatic_scope_exit_nested_switch.c
int32 nested_fallthrough_keeps_local_alive() {
    int32 result = 0;
    switch (0) {
        case 0:
            switch (0) {
                case 0:
                    int32 a[1];
                    a[0] = 7;
                case 1:
                    result = a[0];
                    break;
                default:
                    result = 0;
                    break;
            }
            break;
        default:
            break;
    }
    return result;
}

int32 nested_return_reads_before_cleanup() {
    switch (0) {
        case 0:
            switch (0) {
                case 0:
                    int32 a[1];
                    a[0] = 9;
                    return a[0];
                default:
                    return 0;
            }
        default:
            return 0;
    }
}
```

```click
verifying "automatic_scope_exit_nested_switch.c";

int32 nested_fallthrough_keeps_local_alive() {
    ensures result == 7 by auto;
}

int32 nested_return_reads_before_cleanup() {
    ensures result == 9 by auto;
}
```

```expect
pass
```
