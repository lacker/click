```c filename=echo.c
int32 echo(int32 x) { return x; }
int32 other(int32 x) { return x; }
```
```click
verifying "echo.c";
resource Marker() { field value: int32; }
contract int32 Echo(int32 x) {
    owns cell: Marker();
    ensures cell.value == old(cell.value);
    ensures result == x;
}
int32 echo(int32 x) {
    owns marker: Marker();
    ensures marker.value == old(marker.value);
    ensures result == x;
}
int32 other(int32 x) {
    owns marker: Marker();
    ensures marker.value == old(marker.value);
    ensures result == x;
}
theorem echo_is_echo() executes echo(int32 x) {
    ensures Echo(&echo) as { cell: c } by {
        step(other, { marker: c });
        close();
    }
}
```
```expect
fail: requires a call to `other` at the current frontier
```
