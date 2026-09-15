# conditional goto does not discard the jumping path

The cleanup label is reached with `value == 1` on the jump path, so the
fallthrough path's `value == 2` fact cannot become a fact of their join.

```c filename=forward_goto_conditional_wrong_join.c
int32 conditional_cleanup_wrong_join(int32 failed) {
    int32 value;
    value = 1;
    if (failed)
        goto cleanup;
    value = 2;
cleanup:
    return value;
}
```

```click
verifying "forward_goto_conditional_wrong_join.c";

int32 conditional_cleanup_wrong_join(int32 failed) {
    ensures result == 2;
} by {
    execute();
    normalize();
}
```

```expect
fail: `conditional_cleanup_wrong_join.contract` path 0, tactic 1: `normalize` did not prove any current proposition goal
```
