# local array loop verifies bounded stack array writes

This checks that bounded execution can prove a small loop that writes a local
array object and reads it back.

```c filename=local_array_loop.c
int32 local_array_loop() {
    int32 a[3];
    int32 i;
    i = 0;
    while (i < 3) {
        a[i] = i;
        i = i + 1;
    }
    return a[2];
}
```

```click
verifying "local_array_loop.c";

int32 local_array_loop() {
    ensures returns_second: result == 2 by auto;
}
```

```expect
pass
```
