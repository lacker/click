# free permission can be returned

This checks that `free(...)` can be transferred through a helper and returned in
the helper's resource summary.

```c filename=borrow_free.c
int32 borrow_free(int32 p[]) {
    return 0;
}
```

```c filename=call_borrow_free.c
int32 call_borrow_free(int32 p[]) {
    int32 value;
    value = borrow_free(p);
    return value;
}
```

```click
verifying "borrow_free.c";
verifying "call_borrow_free.c";

int32 borrow_free(int32 p[]) {
    requires free(p[0..1]);

    ensures free(p[0..1]) by auto;
}

int32 call_borrow_free(int32 p[]) {
    requires free(p[0..1]);

    ensures free(p[0..1]) by auto;
}
```

```expect
pass
```
