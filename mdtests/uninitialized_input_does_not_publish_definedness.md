# Uninitialized input ownership does not publish initialized reads

```c filename=uninitialized_input.c
void f(int32 *p, int32 n) {}
```
```click
verifying "uninitialized_input.c";
void f(int32 *p, int32 n) {
    requires 0 < n;
    owns uninitialized(p[0..n]);
} by {
    have forall (j: int32) { 0 <= j and j < n implies defined(p[j]) } by { close(); }
}
```
```expect
fail: could not establish `forall (j: int32) { 0 <= j and j < n implies defined(p[j]) }`
```
