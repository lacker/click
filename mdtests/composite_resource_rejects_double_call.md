# composite resource rejects double call

This checks that a composite resource still behaves linearly through a
call summary. After the first `consume_uncalled(flag)`, the caller no longer has
`uncalled(flag)`, so the second call is rejected.

```c filename=consume_uncalled.c
int32 consume_uncalled(int32 flag[]) {
    return 0;
}
```

```c filename=call_twice.c
int32 call_twice(int32 flag[]) {
    int32 status;
    status = consume_uncalled(flag);
    status = consume_uncalled(flag);
    return status;
}
```

```click
resource uncalled(flag: int32*) {
    contains write(flag[0..1]);
    fact flag[0] == 0;
}

verifying "consume_uncalled.c";
verifying "call_twice.c";

int32 consume_uncalled(int32 flag[]) {
    requires uncalled(flag);
}

int32 call_twice(int32 flag[]) {
    requires uncalled(flag);

    ensures result == 0 by auto;
}
```

```expect
fail: missing resource fact `uncalled(flag)`
```
