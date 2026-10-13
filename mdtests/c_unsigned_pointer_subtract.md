# Pointer subtraction preserves unsigned offsets and element width

```c filename=offset.c
void* identity(void* p) { return p - 0UL; }
int32 byte_offset() {
    char bytes[3];
    void* p = &bytes[2];
    void* q = p - 1UL;
    return q == (void*)&bytes[1] && q + 1UL == p;
}
int32 typed_offset() {
    int32 cells[3];
    int32* p = &cells[2];
    int32* q = p - 1UL;
    return q == &cells[1];
}
```

```click
verifying "offset.c";
void* identity(void* p) { ensures result == p; } by { execute(); normalize(); }
int32 byte_offset() { ensures result == 1; } by { execute(); normalize(); }
int32 typed_offset() { ensures result == 1; } by { execute(); normalize(); }
```

```expect
pass
```
