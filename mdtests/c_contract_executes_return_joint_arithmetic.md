# Joint callback guarantees support explicit arithmetic reasoning

```click
theorem zero_increment_defined(value: int32) {
    requires value == 0;
    ensures defined(value + 1) by { simp(); }
}
theorem zero_successor(value: int32, returned: int32) {
    requires returned == 0;
    requires value == returned + 1;
    ensures value == 1;
}
resource Cell(p: int32*) { owns p[0..1]; }
contract int32 First(int32* p) { owns p[0..1]; ensures result == 0; }
contract int32 Second(int32* p) { owns p[0..1]; ensures p[0] == result + 1; }
contract int32 Target(int32* p) { owns Cell(p); ensures result == 0; ensures p[0] == 1; }
theorem lift(callback: int32 (*)(int32*)) executes callback(int32* cell) {
    requires First(callback);
    requires Second(callback);
    ensures Target(callback) by {
        unfold(Cell(cell)); step(First);
        have result == 0 by { assumption(); }
        apply(zero_increment_defined(result));
        have cell[0] == result + 1 by {
            extract(cell[0] == result + 1); assumption();
        }
        apply(zero_successor(cell[0], result));
        fold(Cell(cell)); simp();
    }
}
```

```expect
pass
```
