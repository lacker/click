# Terminal modular exceptional call

A direct call whose normal continuation is a return checks the caller's
normal and exceptional contracts against the corresponding callee claims.
The C implementation is unchanged and contains no throw syntax; the caller
uses the callee's verified modular interface.

```c filename=exceptional_terminal_call.c
int32 helper(int32 x) {
    return x;
}

int32 caller(int32 x) {
    return helper(x);
}
```

```click
verifying "exceptional_terminal_call.c";

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
