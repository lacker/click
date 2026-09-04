# file-scope static arrays remain private to their translation units

Same-named file-scope `static` arrays in different source files have separate
stable storage, just like same-named scalar statics.

```c filename=alpha.c
static int32 values[2] = {1, 2};

int32 alpha() {
    values[0] = values[0] + 1;
    return values[0] + values[1];
}
```

```c filename=beta.c
static int32 values[2] = {10, 20};

int32 beta() {
    values[0] = values[0] + 1;
    return values[0] + values[1];
}
```

```c filename=runner.c
int32 alpha();
int32 beta();

int32 run() {
    int32 first = alpha();
    int32 second = beta();
    return first + second;
}
```

```click
verifying "alpha.c";
verifying "beta.c";
verifying "runner.c";

int32 alpha() {
    mutable values[0..2] by auto;
    ensures result == 4 by auto;
}

int32 beta() {
    mutable values[0..2] by auto;
    ensures result == 31 by auto;
}

int32 run() {
    ensures result == 35 by auto;
}
```

```expect
pass
```
