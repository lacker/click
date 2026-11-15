# A prepared fold reads current memory through a state-valued pointer

The pointer argument is a value, not an old array view. The cell starts at
zero and is written to one before the fold; its prerequisite must refer to
the current cell. The explicit `have` isolates that fact from folding.

```c filename=fold.c
struct holder { int32* data; };
void make(struct holder* h) { h->data[0] = 1; }
```
```click
verifying "fold.c";
resource ones(p: int32*) {
    field next: int32;
    owns p[0..1];
    fact 0 <= next;
    fact forall(k: int32) { next <= k and k < 1 implies p[k] == 1 };
}
void make(struct holder* h) {
    views *h;
    consumes h->data[0..1];
    requires forall(k: int32) { 0 <= k and k < 1 implies h->data[k] == 0 };
    produces z: ones(old(h->data));
} by {
    step();
    have forall(k: int32) { 0 <= k and k < 1 implies load_int32(old(h->data) + k) == 1 } by { solve(); }
    let z = fold(ones(old(h->data)), {next: 0});
    step_until(function.exit);
    solve();
}
```
```expect
pass
```
