# The sequential profile rejects concurrency-only builtins

Sequential access evidence does not model atomics or synchronization.

```c filename=sequential_concurrency_rejected.c
int32 unsupported(int32 value) {
    return __atomic_load_n(&value, 0);
}
```

```click
verifying "sequential_concurrency_rejected.c";
```

```expect
fail:sequential access primitives only
```
