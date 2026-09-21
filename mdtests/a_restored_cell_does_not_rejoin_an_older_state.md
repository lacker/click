# writing a cell back does not put the state back

The third store writes `a[i]` with exactly the value the first store wrote, so
the cell map after it is the cell map after the first store. It is not the same
state: in between, `a[j]` was written, and `a[j]` may be `a[m]`.

A snapshot that re-interned onto the first store's node would take the write to
`a[j]` off the recorded history, and the read at the end would be framed back to
function entry. The forget the second store performed is part of this snapshot's
identity, so it cannot.

```c filename=a_restored_cell_does_not_rejoin_an_older_state.c
int32 write_back_then_read(int32* a, int32 i, int32 j, int32 m) {
    a[i] = 7;
    a[j] = 0;
    a[i] = 7;
    return a[m];
}
```

```click
verifying "a_restored_cell_does_not_rejoin_an_older_state.c";

int32 write_back_then_read(int32* a, int32 i, int32 j, int32 m) {
    owns a[0..8];
    requires 0 <= i;
    requires i < 8;
    requires 0 <= j;
    requires j < 8;
    requires 0 <= m;
    requires m < 8;
    requires m != i;
    ensures result == old(a[m]);
} by {
    execute();
    simp();
}
```

```expect
fail: result == old(a[m])
```
