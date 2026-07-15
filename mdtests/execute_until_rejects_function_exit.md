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
        execute_rest();
        execute_until(statement(0));
        simp();
    }
}
```

```expect
fail: `execute_until(statement(0))` cannot run after execution already reached function exit
```
