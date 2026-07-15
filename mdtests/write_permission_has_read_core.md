# write permission has read core

This checks that owned memory carries the same stable view as viewed memory
while still returning the write resource.

```c filename=write_read_same_twice.c
int32 write_read_same_twice(int32 p[]) {
    int32 first;
    int32 second;
    first = p[0];
    second = p[0];
    if (first == second) {
        return 1;
    } else {
        return 0;
    }
}
```

```click
verifying "write_read_same_twice.c";

int32 write_read_same_twice(int32 p[]) {
    consumes p[0..1];

    ensures result == 1 by auto;
    produces p[0..1] by auto;
}
```

```expect
pass
```
