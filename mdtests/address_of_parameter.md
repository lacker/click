# parameter addresses use callee-owned storage

An ordinary C parameter is a local object in the callee. Taking its address
must be valid, and a callee parameter must not alias a caller local merely
because both declarations use the same spelling.

```c filename=write_parameter.c
int32 write_parameter(int32 n) {
    int32* p;
    p = &n;
    *p = 5;
    return n;
}
```

```c filename=same_named_parameter.c
int32 same_named_parameter(int32 n) {
    int32* p;
    p = &n;
    write_parameter(1);
    return *p;
}
```

```click
verifying "write_parameter.c";
verifying "same_named_parameter.c";

int32 write_parameter(int32 n) {
    ensures result == 5 by auto;
}

int32 same_named_parameter(int32 n) {
    ensures result == n by auto;
}
```

```expect
pass
```
