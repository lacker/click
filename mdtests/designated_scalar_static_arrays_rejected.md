# scalar array designators reject duplicate elements

An index designator may initialize a scalar array element only once in this
bounded slice. Repeating an element would make the final value depend on
overwriting initializer state instead of exposing a deterministic source
diagnostic.

```c filename=duplicate.c
int32 values[3] = {
    [1] = 2,
    [1] = 4
};

int32 run() {
    return values[1];
}
```

```click
verifying "duplicate.c";
```

```expect
fail: duplicate designator
```
