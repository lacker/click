# Callback refinement proves a symbolic borrowed subrange

The named contract owns a symbolic slice.  Bounds on `index` show that the
concrete callback's one-cell view lies inside it.  This uses the same indexed
range reasoning as ordinary resource transfer.

```c filename=symbolic_borrowed_callback_subrange.c
int32 read_at(int32* state, int32 position, int32 count) {
    return state[position];
}

int32 apply_read(
    int32 (*read)(int32*, int32, int32),
    int32* cells,
    int32 index,
    int32 length
) {
    return read(cells, index, length);
}

int32 symbolic_borrowed_subrange_caller(
    int32* cells,
    int32 index,
    int32 length
) {
    return apply_read(&read_at, cells, index, length);
}
```

```click
verifying "symbolic_borrowed_callback_subrange.c";

contract int32 ReadAt(int32* cells, int32 index, int32 length) {
    requires 0 <= index;
    requires index < length;
    owns cells[0..length];
    ensures result == cells[index];
}

int32 read_at(int32* state, int32 position, int32 count) {
    requires 0 <= position;
    requires position < count;
    views state[position..position + 1];
    ensures result == state[position];
} by {
    execute();
    simp();
}

int32 apply_read(
    int32 (*read)(int32*, int32, int32),
    int32* cells,
    int32 index,
    int32 length
) {
    requires ReadAt(read);
    requires 0 <= index;
    requires index < length;
    owns cells[0..length];
    ensures result == cells[index];
} by {
    execute();
    simp();
}

int32 symbolic_borrowed_subrange_caller(
    int32* cells,
    int32 index,
    int32 length
) {
    requires 0 <= index;
    requires index < length;
    owns cells[0..length];
    ensures result == cells[index];
} by {
    execute();
    simp();
}
```

```expect
pass
```
