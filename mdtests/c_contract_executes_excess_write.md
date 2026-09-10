# The public contract's owned footprint remains an obligation

`Buffered` views the whole buffer and owns only its first cell, so lifting a
`Raw` callback that owns both cells is rejected: the theorem cannot hand the
callback ownership the public contract never gave it.

```click
resource Buffer(data: int32*) { owns data[0..2]; }
contract void Raw(int32* data) { owns data[0..2]; }
contract void Buffered(int32* data) { views Buffer(data); owns data[0..1]; }
theorem lift(callback: void (*)(int32*)) executes callback(int32* data) {
    requires Raw(callback);
    ensures Buffered(callback) by {
        unfold(Buffer(data)); step(Raw); fold(Buffer(data)); simp();
    }
}
```

```expect
fail: missing resource fact `owns data[0..2]`
```
