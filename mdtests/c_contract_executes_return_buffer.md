# Return-valued callback refinement preserves ownership and relates the result to memory

```c filename=buffer.c
int32 set_one(int32* cell) { *cell = 1; return *cell; }
int32 invoke(int32 (*callback)(int32*), int32* cell) { return callback(cell); }
int32 caller(int32* cell) { return invoke(&set_one, cell); }
```

```click
resource Buffer(cell: int32*) { owns cell[0..1]; }
contract int32 Raw(int32* cell) {
    owns cell[0..1]; mutable cell[0..1];
    ensures cell[0] == 1;
    ensures result == cell[0];
}
contract int32 Buffered(int32* cell) {
    owns Buffer(cell); mutable cell[0..1];
    ensures cell[0] == 1;
    ensures result == 1;
}
theorem lift(callback: int32 (*)(int32*)) executes callback(int32* data) {
    requires Raw(callback);
    ensures Buffered(callback) by {
        unfold(Buffer(data));
        step(Raw);
        have result == data[0] by { assumption(); }
        fold(Buffer(data)); frame(); simp();
    }
}
verifying "buffer.c";
int32 set_one(int32* cell) {
    owns cell[0..1]; mutable cell[0..1];
    ensures cell[0] == 1; ensures result == cell[0];
} by { execute(); frame(); simp(); }
int32 invoke(int32 (*callback)(int32*), int32* cell) {
    requires Raw(callback);
    owns Buffer(cell); mutable cell[0..1];
    ensures result == 1;
} by { apply(lift(callback)); step(Buffered); execute(); frame(); simp(); }
int32 caller(int32* cell) {
    owns Buffer(cell); mutable cell[0..1]; ensures result == 1;
} by { execute(); frame(); simp(); }
```

```expect
pass
```
