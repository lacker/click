# An indexed read equality cites its index fact

The load-address proof needs `index == 0`. The other aliases are connected
facts, but do not belong in the emitted proof's premise selection. Keep the
smart proof and its checked transcription valid after narrowing that selection.

```c filename=same.c
int32 same(int32* data, int32 index, int32 x0, int32 x1) { return 0; }
```

```click
verifying "same.c";
int32 same(int32* data, int32 index, int32 x0, int32 x1) {
    owns data[0..2];
    requires index == 0;
    requires index == x0;
    requires index == x1;
    ensures result == 0;
} by {
    have data[index] == data[0] by { close(); }
}
```

```expect
pass
```
