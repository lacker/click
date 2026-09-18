# An overlapping copy is refused by the separation precondition

The `memcpy` contract requires `separate` source and destination ranges: it
is a non-overlapping copy primitive. Copying within one allocation with
overlapping source and destination cannot establish that separation, so the
call is refused. The overlapping bytes are named in the diagnostic; no byte
moves and no representation is established.

```c filename=overlapping_memcpy.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);
int f(void) {
    unsigned char *buf = malloc(16);
    if (buf == 0) { return -1; }
    memcpy(buf + 2, buf, 8);
    free(buf);
    return 0;
}
```

```click
verifying "overlapping_memcpy.c";

int f() {
    ensures result == 0 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: separate(
```
