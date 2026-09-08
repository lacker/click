# Data-only duplicate definitions are still rejected

```c filename=reader.c
extern int32 value;
int32 read() { return value; }
```

```c filename=first.c
int32 value = 1;
```

```c filename=second.c
int32 value = 2;
```

```click
verifying "reader.c";
verifying "first.c";
verifying "second.c";
```

```expect
fail: multiple definitions of global `value`
```
