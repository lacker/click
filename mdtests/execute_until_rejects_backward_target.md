# execute until rejects a backward target

```c filename=execute_until_backward.c
int32 execute_until_backward(int32 x) {
    int32 y;
    y = x;
    return y;
}
```

```click
verifying "execute_until_backward.c";

int32 execute_until_backward(int32 x) {
    ensures result == x by {
        step();
        execute_until(statement(0));
        execute();
        simp();
    }
}
```

```expect
fail: `execute_until(statement(0))` cannot move backward from statement(1)
```
