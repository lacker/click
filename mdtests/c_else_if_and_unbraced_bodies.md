# `else if` and unbraced C control-flow bodies

This keeps ordinary C control-flow spelling intact: an `else if` is a nested
`if`, and each arm is one statement rather than an invented block.

```c filename=classify.c
int32 classify(int32 x) {
    if (x < 0)
        return -1;
    else if (x == 0)
        return 0;
    else
        return 1;
}
```

```click
verifying "classify.c";

int32 classify(int32 x) {
    requires x > 0;
    ensures result == 1;
}
```

```expect
pass
```
