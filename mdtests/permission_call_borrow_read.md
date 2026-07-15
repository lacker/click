# permission call borrows read access

This checks that a helper can borrow read permission from a caller with write
permission. The read requirement is copyable, so the caller can still write the
same cell after the helper returns.

```c filename=borrow_first.c
int32 borrow_first(int32 p[]) {
    return p[0];
}
```

```c filename=borrow_then_write.c
int32 borrow_then_write(int32 p[]) {
    int32 value;
    value = borrow_first(p);
    p[0] = 1;
    return p[0];
}
```

```click
verifying "borrow_first.c";
verifying "borrow_then_write.c";

int32 borrow_first(int32 p[]) {
    requires loadable(p[0..1]);
    views p[0..1];

}

int32 borrow_then_write(int32 p[]) {
    requires loadable(p[0..1]);
    consumes p[0..1];

    ensures returns_written: result == 1 by auto;
    produces p[0..1] by auto;
}
```

```expect
pass
```
