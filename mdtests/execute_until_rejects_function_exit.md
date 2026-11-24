# execute until rejects execution after function exit

```c filename=execute_until_after_exit.c
int32 execute_until_after_exit(int32 x) {
    return x;
}
```

```click
verifying "execute_until_after_exit.c";

int32 execute_until_after_exit(int32 x) {
    ensures result == x by {
        step_until(function.exit);
        step_until(region(0).entry);
        close();
    }
}
```

```expect
fail: `step_until(region(0).entry)` cannot run after execution already reached function exit
```
