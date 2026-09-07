# Inferred aggregate bounds must agree with external declarations

```c filename=reader.c
struct E { int32 x; };
extern struct E table[3];
int32 read() { return table[0].x; }
```

```c filename=definition.c
struct E { int32 x; };
struct E table[] = {{1}, {2}};
int32 anchor() { return table[1].x; }
```

```click
verifying "reader.c";
verifying "definition.c";
```

```expect
fail: conflicting declarations for aggregate global array `table`
```
