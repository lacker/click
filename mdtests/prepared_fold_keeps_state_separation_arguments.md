# MemoryState-valued separation fact in a prepared fold

```c filename=fold.c
void make(int32* p, int32* q) {}
```
```click
verifying "fold.c";
resource separated(p: int32*, q: int32*) {
    fact separate(memory(p[0..1]), memory(q[0..1]));
}
void make(int32* p, int32* q) {
    requires separate(memory(p[0..1]), memory(q[0..1]));
    produces separated(p, q);
} by {
    fold(separated(old(p), old(q)));
    step_until(function.exit);
    solve();
}
```
```expect
pass
```
