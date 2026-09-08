# Data-only translation units contribute every kind of global object

```c filename=reader.c
struct E { int32 x; };
extern int32 scalar;
extern int32 values[];
extern struct E object;
extern struct E entries[];
extern int32 *alias;
int32 read() { return scalar + values[1] + object.x + entries[0].x + *alias; }
```

```c filename=data.c
struct E { int32 x; };
int32 scalar = 2;
int32 values[] = {3, 4};
struct E object = {5};
struct E entries[] = {{6}};
int32 *alias = &scalar;
```

```click
verifying "reader.c";
verifying "data.c";
int32 read() { ensures result == 19 by auto; }
```

```expect
pass
```
