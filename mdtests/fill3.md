# fill3 verifies a three-element store loop

This checks that `valid_range(p, 12)` is enough to prove three `int32`
stores and a final load from `p + 2`.

```c filename=fill3.c
int32 fill3(int32* p) {
    int32 i;
    i = 0;
    while (i < 3) {
        *(p + i) = i;
        i = i + 1;
    }
    return *(p + 2);
}
```

```click
verifying "fill3.c";

int32 fill3(int32* p) {
    returns_second {
        requires valid_range(p, 12);
        ensures result == 2;

        proof {
            auto;
        }
    }
}
```

```expect
pass
```
