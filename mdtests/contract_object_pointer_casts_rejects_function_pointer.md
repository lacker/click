# Object-pointer contract casts reject function pointers

```c filename=function.c
int32 run(int32 (*callback)(int32)) { return 0; }
```

```click
verifying "function.c";
int32 run(int32 (*callback)(int32)) {
    ensures (void*)callback == (void*)callback;
} by { execute(); simp(); }
```

```expect
fail: expects an object pointer operand
```
