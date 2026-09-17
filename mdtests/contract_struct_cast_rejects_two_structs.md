# A contract casts a `void *` parameter to one struct only

Proof synthesis reads a cast parameter with a single layout, so casting the
same parameter to two structs in one block is rejected where the second cast
is written.

```c filename=two_casts.c
struct a {
    int x;
};

struct b {
    int y;
};

int pick(void *argument) {
    struct a *object = argument;
    return object->x;
}
```

```click
verifying "two_casts.c";

int32 pick(void *argument) {
    views ((struct a *)argument)->x;
    ensures result == ((struct b *)argument)->y;
} by {
    execute();
    simp();
}
```

```expect
fail: parameter `argument` is already cast to `struct a`; a contract casts a parameter to one struct
```
