# free permission splits and rejoins

This checks that a caller can pass one cell from a larger free range to a
helper, keep the residue, and regain the full free range when the helper
returns its subrange.

```c filename=borrow_first_free.c
int32 borrow_first_free(int32 p[]) {
    return 0;
}
```

```c filename=borrow_first_from_two_free.c
int32 borrow_first_from_two_free(int32 p[]) {
    int32 value;
    value = borrow_first_free(p);
    return value;
}
```

```click
verifying "borrow_first_free.c";
verifying "borrow_first_from_two_free.c";

int32 borrow_first_free(int32 p[]) {
    requires free(p[0..1]);

    ensures free(p[0..1]) by auto;
}

int32 borrow_first_from_two_free(int32 p[]) {
    requires free(p[0..2]);

    ensures free(p[0..2]) by auto;
}
```

```expect
pass
```
