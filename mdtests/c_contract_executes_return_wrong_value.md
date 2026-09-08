# Ownership adaptation cannot strengthen an unsupported returned value

```click
resource Cell(p: int32*) { owns p[0..1]; }
contract int32 Raw(int32* p) { owns p[0..1]; ensures result == 0; }
contract int32 Boxed(int32* p) { owns Cell(p); ensures result == 1; }
theorem lift(callback: int32 (*)(int32*)) executes callback(int32* cell) {
    requires Raw(callback);
    ensures Boxed(callback) by { unfold(Cell(cell)); step(Raw); fold(Cell(cell)); simp(); }
}
```

```expect
fail: unclosed goal
```
