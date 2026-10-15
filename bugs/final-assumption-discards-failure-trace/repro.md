# Final failed assumption trace
```c filename=f.c
void f(int32 *cell, int32 value) { *cell = value; }
```
```click
verifying "f.c";
void f(int32 *cell, int32 value) {
    owns cell[0..1];
    ensures cell[0] == value;
    ensures cell[0] == value + 1;
} by {
    step(); step();
    have cell[0] == value by { simp(); }
    assumption(); assumption(); assumption();
}
```
```expect
fail: found no available fact
```
