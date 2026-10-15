# Independently opened owners separate through transitive pointer equality

The ownership lookup must use the shared address classes rather than requiring
a redundant direct pointer equality.

```c filename=f.c
void f(int32 *a, int32 *b, int32 *x, int32 *y) { return; }
```
```click
verifying "f.c";
resource cell(p: int32*) { field tag: int32; owns p[0]; }
void f(int32 *a, int32 *b, int32 *x, int32 *y) {
    owns left: cell(a);
    owns right: cell(b);
    requires a == x;
    requires x == y;
    ensures true;
} by {
    unfold(left); unfold(right);
    have separate(memory(y[0]), memory(b[0])) by { assumption(); }
    fold(left); fold(right); execute(); normalize();
}
```

```expect
pass
```
