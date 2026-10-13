# A `long` function declared with a `long long` result in another file is refused

Calling a function through a declaration whose type is not compatible with its
definition is undefined behavior (C11 6.5.2.2p9), and `long long` is not
compatible with `long`.

```c filename=data.c
long width(void) { return 8; }
```

```c filename=main.c
long long width(void);
int run(int value) { return value; }
```

```click
verifying "data.c";
verifying "main.c";

long width() {
    ensures result == 8 by auto;
}

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail: conflicting C function declarations for `width`
```
