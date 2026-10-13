# computed result expression verification

This checks that an `ensures` clause can use a small Click's C integer expression on
the right side of `result ==`.

```c filename=three.c
int32 three() {
    return 3;
}
```

```click
verifying "three.c";

int32 three() {
    ensures result == 1 + 2 by auto;
}
```

```expect
pass
```

