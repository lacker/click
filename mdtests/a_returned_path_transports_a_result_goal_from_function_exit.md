# A returned path transports a `result` goal from function exit

`return a < b;` forks inside one expression, so each returned path has its
own `result`. Once a path has returned, `at(function.exit, ...)` reads its
current state and can name `result`, so one transport closes the goal on
every path without naming the path's value. A false claim is not
transported: the source must still hold on each path.

```c filename=exit_transport.c
int32 is_less(uint32 a, uint32 b) {
    return a < b;
}
```

```click
verifying "exit_transport.c";

int32 is_less(uint32 a, uint32 b) {
    ensures result == 0 or result == 1;
} by {
    execute();
    have result == 0 or result == 1 by {
        transport(at(function.exit, result == 0 or result == 1), result == 0 or result == 1) using {
        }
    }
    assumption();
}
```

```expect
pass
```
