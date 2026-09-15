# conditional forward goto

A `goto` in an `if` arm may resume at a later direct function-body label. The
jumping and fallthrough paths keep their own state until they meet at the
label.

```c filename=forward_goto_conditional.c
int32 conditional_cleanup(int32 failed) {
    int32 value;
    value = 1;
    if (failed) {
        goto cleanup;
    }
    value = 2;
cleanup:
    return value;
}

int32 conditional_cleanup_step(int32 failed) {
    int32 value;
    value = 1;
    if (failed)
        goto cleanup;
    value = 2;
cleanup:
    return value;
}

int32 skip_conditional(int32 flag) {
    int32 value;
    value = 1;
    goto done;
    if (flag)
        value = 98;
    else
        value = 99;
done:
    return value;
}
```

```click
verifying "forward_goto_conditional.c";

int32 conditional_cleanup(int32 failed) {
    ensures result == (if failed != 0 { 1 } else { 2 });
} by {
    execute();
    simp();
}

int32 conditional_cleanup_step(int32 failed) {
    requires failed != 0;
    ensures result == 1;
} by {
    step();
    step();
    step();
    step();
    step();
    normalize();
}

int32 skip_conditional(int32 flag) {
    ensures result == 1;
} by {
    execute();
    normalize();
}
```

```expect
pass
```
