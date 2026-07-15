# known function call verification

This checks that `.click` verification builds a function environment from all
verified C0 sources and can execute a known helper call.

```c filename=increment.c
int32 increment(int32 x) {
    return x + 1;
}
```

```c filename=caller.c
int32 caller() {
    int32 result;
    result = increment(41);
    return result;
}
```

```click
verifying "increment.c";
verifying "caller.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures returns_incremented_value: result == x + 1 by auto;
}

int32 caller() {
    ensures returns_incremented_value: result == 42 by auto;
}
```

```expect
pass
```
