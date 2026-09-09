# A returned const view cannot be passed to a mutable callback parameter

```c filename=main.c
int bad(const int *(*view)(int *), int (*use)(int *), int *p) {
    return use(view(p));
}
```

```click
verifying "main.c";
int bad(const int *(*view)(int *), int (*use)(int *), int *p) { ensures result == 0; }
```

```expect
fail: const
```
