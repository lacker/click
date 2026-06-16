# bounded loop verification

This checks the current bounded loop path: a loop with concrete state can be
unrolled by `auto` until it reaches the return.

```c filename=bounded_loop.c
int32 count_to_three() {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "bounded_loop.c";

int32 count_to_three() {
    ensures returns_three: result == 3 by auto;
}
```

```expect
pass
```
