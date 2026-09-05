# const pointer views reject stores

A pointer-to-const parameter may read its pointee but cannot be used as a
store target.

```c filename=const_pointer.c
int32 bad(const int32 *values) {
    values[0] = 3;
    return 0;
}
```

```click
verifying "const_pointer.c";
```

```expect
fail:const-qualified
```
