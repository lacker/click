# A signed byte keeps its negative value through storage and calls

A `signed char` holding `-1` promotes to the `int` `-1`, never to `255`. The
value survives a local, a file-scope object and array, a call argument and
return, a `const` pointer view, and a store through a pointer, at both ends of
the signed-byte range.

```c filename=signed_byte_flow.c
signed char low = -128;
signed char table[2] = {-128, 127};

int minus_one(void) { signed char x = -1; return x; }
int read_globals(void) { return low + table[1]; }
signed char pass(signed char value) { return value; }
int call_ends(void) {
    int a = pass(-128);
    int b = pass(127);
    return a + b;
}
int sum_view(const signed char *p) { return p[0] + p[1]; }
int view_caller(void) {
    signed char values[2];
    values[0] = -1;
    values[1] = -2;
    return sum_view(values);
}
void store(signed char *p, signed char value) { *p = value; }
int store_caller(void) {
    signed char cell = 0;
    store(&cell, -100);
    return cell;
}
```

```click
verifying "signed_byte_flow.c";

int minus_one() { ensures result == -1 by auto; }
int read_globals() {
    requires low == -128;
    requires table[1] == 127;
    ensures result == -1 by auto;
}
signed char pass(signed char value) { ensures result == value by auto; }
int call_ends() { ensures result == -1 by auto; }
int sum_view(const signed char *p) {
    views p[0..2];
    ensures result == p[0] + p[1] by auto;
}
int view_caller() { ensures result == -3 by auto; }
void store(signed char *p, signed char value) {
    requires viewable(p[0..1]);
    consumes p[0..1];
    produces p[0..1];
    ensures p[0] == value by auto;
}
int store_caller() { ensures result == -100 by auto; }
```

```expect
pass
```
