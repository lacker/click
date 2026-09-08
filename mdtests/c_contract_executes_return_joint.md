# Selected resource transitions share the same return value across interfaces

```click
resource Cell(p: int32*) { owns p[0..1]; }
contract int32 First(int32* p) { owns p[0..1]; mutable p[0..1]; ensures result == 0; }
contract int32 Second(int32* p) { owns p[0..1]; mutable p[0..1]; ensures p[0] == result; }
contract int32 Target(int32* p) { owns Cell(p); mutable p[0..1]; ensures result == 0; ensures p[0] == 0; }
theorem lift(callback: int32 (*)(int32*)) executes callback(int32* cell) {
    requires First(callback);
    requires Second(callback);
    ensures Target(callback) by {
        unfold(Cell(cell)); step(First);
        have result == 0 by { assumption(); }
        have cell[0] == result by { assumption(); }
        have cell[0] == 0 by {
            rewrite(cell[0] == result);
            rewrite(result == 0);
            simp();
        }
        fold(Cell(cell)); frame(); simp();
    }
}
```

```expect
pass
```
