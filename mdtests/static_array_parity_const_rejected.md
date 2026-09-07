# Inferred multidimensional static arrays reject const writes

```c filename=bad.c
int32 bad() {
    static const int32 table[][2] = {{1}};
    table[0][1] = 4;
    return table[0][1];
}
```

```click
verifying "bad.c";
```

```expect
fail:const-qualified
```
