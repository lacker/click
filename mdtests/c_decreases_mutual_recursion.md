# mutually recursive C functions share a decreasing discipline

```c filename=c_decreases_even.c
int32 even(int32 n) {
    int32 result;
    if (n > 0) {
        result = odd(n - 1);
        return result;
    }
    return 1;
}
```

```c filename=c_decreases_odd.c
int32 odd(int32 n) {
    int32 result;
    if (n > 0) {
        result = even(n - 1);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_even.c";
verifying "c_decreases_odd.c";

int32 even(int32 n) {
    decreases n;
    ensures result >= 0 by auto;
}

int32 odd(int32 n) {
    decreases n;
    ensures result >= 0 by auto;
}
```

```expect
pass
```
