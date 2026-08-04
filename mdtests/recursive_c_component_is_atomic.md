# one bad recursive member rejects the whole verification transaction

The good member may use the bad member's provisional postcondition while its
body is checked. The finite undefined behavior in the bad member still rejects
the component, so no collection of verified rules is returned.

```c filename=good.c
int32 good(int32 n) {
    int32 result;
    result = bad(n);
    return result;
}
```

```c filename=bad.c
int32 bad(int32 n) {
    int32 zero;
    int32 result;
    zero = 0;
    result = n / zero;
    result = good(result);
    return result;
}
```

```click
verifying "good.c";
verifying "bad.c";

int32 good(int32 n) {
    ensures result == 0 by auto;
}

int32 bad(int32 n) {
    ensures result == 0 by auto;
}
```

```expect
fail: division by zero
```
