# Unknown requires name is diagnosed at its contract clause

```c filename=unknown_name.c
int is_positive(int x) { return x > 0; }
```

```click
verifying "unknown_name.c";
int32 is_positive(int32 x) {
    requires y > 0;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: unknown name `y` in `requires y > 0`
```
