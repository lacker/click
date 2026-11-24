# A retained view still constrains a callee write

The entry contract leaves the relationship between the folded owner and the
view undecided. A call on the equality branch still needs evidence that its
write is separate from the live view.

```c filename=overlap.c
void mutate(int32 *p) { *p = 1; }
int32 observe(int32 *p, int32 *q) {
    int32 value = *q;
    if (p == q) mutate(p);
    return value;
}
```
```click
verifying "overlap.c";
resource item(p: int32*) { owns *p; }
void mutate(int32* p) { owns item(p); } by {
    unfold(item(p));
    step_until(function.exit);
    fold(item(p));
    close();
}
int32 observe(int32* p, int32* q) {
    views *q;
    owns item(p);
    ensures result == *q;
}
```

```expect
fail: prove the write by `mutate` is separate from the live views
```
