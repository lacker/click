# An observed live range does not initialize cells
```c filename=unwritten.c
void unwritten(int32 *p) {}
```
```click
verifying "unwritten.c";
void unwritten(int32 *p) {
 owns uninitialized(p[0..2]);
 ensures defined(p[1]);
} by {
 step_until(function.exit);
 observe(p[0..2]);
 close();
}
```
```expect
fail: defined
```
