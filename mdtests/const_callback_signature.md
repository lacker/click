# Const-returning addresses cannot satisfy mutable-return callback types

```c filename=main.c
const int *view(int *p) { return p; }
int bad(int *p) { int *(*f)(int *) = &view; return 0; }
```

```click
verifying "main.c";
int bad(int *p) { ensures result == 0; }
```

```expect
fail: signature
```
