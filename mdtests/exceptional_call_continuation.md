# Modular call with a continuing normal path

The call has two checked successors. Its normal result continues through an
assignment; its exceptional payload exits the caller without executing that
assignment. Both caller claim families are proved from the corresponding
callee family.

```c filename=exceptional_call_continuation.c
int32 helper(int32 x) {
    return x;
}

int32 caller(int32 x) {
    int32 y = helper(x);
    y = x;
    return y;
}
```

```click
verifying "exceptional_call_continuation.c";

int32 helper(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}

int32 caller(int32 x) throws int32 {
    ensures result == x;
    exceptional ensures exception == 7;
}
```

```expect
pass
```
