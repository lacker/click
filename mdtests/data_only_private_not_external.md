# Private data-only definitions cannot satisfy an external declaration

```c filename=reader.c
extern int32 value;
int32 read() { return value; }
```

```c filename=data.c
static int32 value = 2;
```

```click
verifying "reader.c";
verifying "data.c";
```

```expect
fail: global `value` is declared `extern` but has no definition
```
