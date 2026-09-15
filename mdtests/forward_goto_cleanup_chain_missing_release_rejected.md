# cleanup chain cannot omit a release

The second-allocation failure path still owns `first`. Replacing the shared
`free_first` cleanup with an ordinary assignment leaves a live allocation at
the function boundary.

```c filename=forward_goto_cleanup_chain_missing_release.c
int32 cleanup_missing_first_release(void) {
    int32* first;
    int32* second;
    int32 result;

    first = malloc(sizeof(int32));
    if (first == 0) {
        result = -1;
        goto out;
    }

    second = malloc(sizeof(int32));
    if (second == 0) {
        result = -2;
        goto free_first;
    }

    result = 0;
    free(second);
free_first:
    result = result;
out:
    return result;
}
```

```click
verifying "forward_goto_cleanup_chain_missing_release.c";

int32 cleanup_missing_first_release() {
    ensures result == -1 or result == -2 or result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: live allocation obligation was neither returned nor freed
```
