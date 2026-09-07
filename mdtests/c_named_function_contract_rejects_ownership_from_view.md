# A borrowed callback contract cannot supply concrete ownership

The direction matters.  A caller satisfying the named contract promises only
a view, so a concrete callback that requires ownership cannot safely be used,
even if this particular implementation only reads the cell.

```c filename=callback_ownership_from_view.c
int32 claims_ownership(int32* state) {
    return state[0];
}

int32 apply_read(int32 (*read)(int32*), int32* cell) {
    return read(cell);
}

int32 ownership_from_view_caller(int32* cell) {
    return apply_read(&claims_ownership, cell);
}
```

```click
verifying "callback_ownership_from_view.c";

contract int32 BorrowedRead(int32* cell) {
    views cell[0..1];
    ensures result == cell[0];
}

int32 claims_ownership(int32* state) {
    owns state[0..1];
    ensures result == state[0];
} by {
    execute();
    simp();
}

int32 apply_read(int32 (*read)(int32*), int32* cell) {
    requires BorrowedRead(read);
    views cell[0..1];
    ensures result == cell[0];
} by {
    execute();
    simp();
}

int32 ownership_from_view_caller(int32* cell) {
    views cell[0..1];
    ensures result == cell[0];
} by {
    execute();
    simp();
}
```

```expect
fail: function `claims_ownership` does not satisfy named contract `BorrowedRead`
```
