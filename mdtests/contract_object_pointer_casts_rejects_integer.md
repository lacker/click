# A contract void-pointer cast requires an object pointer

```c filename=integer.c
struct item { int32 value; };
int32 run(int32 x) { return x; }
```

```click
verifying "integer.c";
int32 run(int32 x) {
    views ((struct item*)(void*)x)->value;
    ensures result == x;
} by { execute(); normalize(); }
```

```expect
fail: expects an object pointer operand
```
