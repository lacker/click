# Inferred arrays preserve const storage and private identity

```c filename=a.c
struct E { int32 x; int32 y; };
static const struct E table[] = {{3}};
int32 a() {
    static const int32 matrix[][2] = {{4}, {6, 7}};
    static const int32 cube[][2][2] = {{{2}}, {{8}}};
    static const struct E local[] = {{5}};
    static int32 zero[2][2];
    return table[0].x + table[0].y + matrix[0][0] + matrix[0][1] + matrix[1][0] + matrix[1][1] + cube[1][0][0] + cube[1][1][1] + local[0].x + local[0].y + zero[1][1];
}
```

```c filename=b.c
struct E { int32 x; int32 y; };
static const struct E table[] = {{9}};
int32 b() { return table[0].x + table[0].y; }
```

```click
verifying "a.c";
verifying "b.c";
int32 a() {
    requires zero[1][1] == 0;
    ensures result == 33 by auto;
}
int32 b() { ensures result == 9 by auto; }
```

```expect
pass
```
