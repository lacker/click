# read permission stable repeated load

This checks that a held viewed-memory resource gives a stable read view: two
loads from the same cell with no intervening write produce the same value.

```c filename=read_same_twice.c
int32 read_same_twice(int32 p[]) {
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
verifying "read_same_twice.c";

int32 read_same_twice(int32 p[]) {
    views p[0..1];

    ensures result == 1 by auto;
}
```

```expect
pass
```
