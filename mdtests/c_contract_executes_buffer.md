# An explicit call proof adapts folded buffer ownership

```click
resource Buffer(data: int32*, count: int32) {
    owns data[0..count];
}

contract void Raw(int32* data, int32 count) {
    requires count >= 0;
    owns data[0..count];
}

contract void Buffered(int32* data, int32 count) {
    requires count >= 0;
    owns Buffer(data, count);
}

theorem raw_is_buffered(callback: void (*)(int32*, int32))
    executes callback(int32* data, int32 count)
{
    requires Raw(callback);
    ensures Buffered(callback) by {
        unfold(Buffer(data, count));
        step(Raw);
        fold(Buffer(data, count));
        simp();
    }
}
```

```expect
pass
```
