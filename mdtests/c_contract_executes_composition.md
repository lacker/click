# A callback execution proof can apply another refinement theorem

```click
resource Buffer(data: int32*) { owns data[0..1]; }
resource Box(data: int32*) { owns Buffer(data); }
contract void Raw(int32* p) { owns p[0..1]; }
contract void Buffered(int32* p) { owns Buffer(p); }
contract void Boxed(int32* p) { owns Box(p); }
theorem lift(callback: void (*)(int32*)) executes callback(int32* data) {
    requires Raw(callback);
    ensures Buffered(callback) by {
        unfold(Buffer(data)); step(Raw); fold(Buffer(data)); simp();
    }
}
theorem box(callback: void (*)(int32*)) executes callback(int32* data) {
    requires Raw(callback);
    ensures Boxed(callback) by {
        apply(lift(callback));
        unfold(Box(data)); step(Buffered); fold(Box(data)); simp();
    }
}
```

```expect
pass
```
