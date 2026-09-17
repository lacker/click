# An execution-backed theorem is reusable at ordinary callback calls

```c filename=buffer_callback.c
void set_cell(int32* data) { data[0] = 1; }
void invoke(void (*callback)(int32*), int32* data) { callback(data); }
void caller(int32* data) { invoke(&set_cell, data); }
```

```click
resource Buffer(data: int32*) { owns data[0..1]; }
contract void Raw(int32* data) { owns data[0..1]; }
contract void Buffered(int32* data) { owns Buffer(data); }

theorem lift(callback: void (*)(int32*)) executes callback(int32* cell) {
    requires Raw(callback);
    ensures Buffered(callback) by {
        unfold(Buffer(cell));
        step(Raw);
        fold(Buffer(cell));
        simp();
    }
}

verifying "buffer_callback.c";
void set_cell(int32* data) {
    owns data[0..1];
} by { execute(); simp(); }

void invoke(void (*callback)(int32*), int32* data) {
    requires Raw(callback);
    owns Buffer(data);
} by {
    apply(lift(callback));
    step(Buffered);
    execute();
    simp();
}

void caller(int32* data) {
    owns Buffer(data);
} by { execute(); simp(); }
```

```expect
pass
```
