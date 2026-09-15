# forward goto cleanup chain releases partial acquisitions

Two allocations are acquired in sequence. Failure of the first allocation
jumps past both cleanup statements, failure of the second releases only the
first allocation, and success releases both allocations through the same
fallthrough cleanup chain.

```c filename=forward_goto_cleanup_chain.c
int32 cleanup_two_allocations(void) {
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
    free(first);
out:
    return result;
}
```

```click
verifying "forward_goto_cleanup_chain.c";

int32 cleanup_two_allocations() {
    ensures result == -1 or result == -2 or result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
