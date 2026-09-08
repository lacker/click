# Explicit resource parameters are declarations, not ownership

The parameter list declares a typed resource handle. `owns cell` separately
requires and returns ownership. Declaring a parameter alone grants nothing.
This fixture checks declarations, not cross-function resource transport.

```click
resource marked_cell(p: int32*) {
    field revision: int32;
}

contract Read(cell: marked_cell(p)) for int32(int32* p) {
    owns cell;
    ensures cell.revision == old(cell.revision);
}

contract Unowned(cell: marked_cell(p)) for int32(int32* p) {
    ensures result == 0;
}
```

```expect
pass
```
