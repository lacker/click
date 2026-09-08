# Select one transition while retaining another applicable guarantee

```c filename=joint.c
void invoke(void (*callback)(int32*), int32* data) { callback(data); }
```

```click
resource Buffer(data: int32*) { owns data[0..2]; }
contract void First(int32* p) { owns p[0..2]; mutable p[0..2]; ensures p[0] == 1; }
contract void Second(int32* p) { owns p[0..2]; mutable p[0..2]; ensures p[1] == 2; }
contract void Buffered(int32* p) {
    owns Buffer(p); mutable p[0..2]; ensures p[0] == 1; ensures p[1] == 2;
}
theorem lift(callback: void (*)(int32*)) executes callback(int32* data) {
    requires First(callback);
    requires Second(callback);
    ensures Buffered(callback) by {
        unfold(Buffer(data)); step(First); fold(Buffer(data)); frame(); simp();
    }
}
verifying "joint.c";
void invoke(void (*callback)(int32*), int32* data) {
    requires First(callback);
    requires Second(callback);
    owns Buffer(data); mutable data[0..2]; ensures data[1] == 2;
} by { apply(lift(callback)); step(Buffered); execute(); frame(); simp(); }
```

```expect
pass
```
