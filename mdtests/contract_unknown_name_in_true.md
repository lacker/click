# Unknown true name is diagnosed at its contract clause

```c filename=unknown_name.c
bool is_positive(int x) { return x > 0; }
```

```click
verifying "unknown_name.c";
bool is_positive(int32 x) {
    requires x > 0;
    ensures result == true;
} by {
    execute();
    simp();
}
```

```expect
fail: unknown name `true` in `ensures result == true`
```
