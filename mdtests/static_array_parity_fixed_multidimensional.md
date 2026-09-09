# function-local static arrays keep one stable object

A fixed-size scalar `static` array is initialized once and reused by later
calls, while contracts can authorize and describe its indexed elements.

```c filename=static_local_arrays.c
int32 increment_twice() {
    static int32 values[1][3] = {{5, 7}};
    values[0][0] = values[0][0] + 1;
    values[0][0] = values[0][0] + 1;
    return values[0][0] + values[0][1] + values[0][2];
}

int32 call_twice() {
    int32 first;
    int32 second;
    first = increment_twice();
    second = increment_twice();
    return second;
}
```

```click
verifying "static_local_arrays.c" as static_local;

int32 increment_twice() {
    owns values[0..3];
    requires values[0][0] > -1000 and values[0][0] < 1000 and values[0][1] > -1000 and values[0][1] < 1000 and values[0][2] > -1000 and values[0][2] < 1000;
    mutable values[0..3] by auto;
    ensures result == old(values[0][0]) + old(values[0][1]) + old(values[0][2]) + 2 by auto;
    ensures values[0][0] == old(values[0][0]) + 2 by auto;
    ensures values[0][1] == old(values[0][1]) by auto;
    ensures values[0][2] == old(values[0][2]) by auto;
}

int32 call_twice() {
    owns static_local::increment_twice::values[0..3];
    requires static_local::increment_twice::values[0][0] == 5 and static_local::increment_twice::values[0][1] == 7 and static_local::increment_twice::values[0][2] == 0;
    ensures result == 16 by auto;
}
```

```expect
pass
```
