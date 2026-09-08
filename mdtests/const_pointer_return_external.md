# External const return contracts preserve the result view

```c filename=caller.c
extern const int *external_view(int *p);
const int *caller(int *p) { return external_view(p); }
```

```click
verifying "caller.c";

extern const int *external_view(int *p) {
    ensures result == p;
}

const int *caller(int *p) {
    ensures result == p;
} by { execute(); simp(); }
```

```expect
pass
```
