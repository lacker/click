# Folding refuses ownership of a different entry cell

The C body writes the cell selected by the original count minus one. Folding
with the original count plus one would claim the next cell instead, and must
fail even though the original cell remains owned.

```c filename=probe.c
int32 probe(int32* p, uint64* count, int32 input) {
    *count = *count - 1;
    p[*count] = input;
    return input;
}
```
```click
verifying "probe.c";
resource cell(p: int32*, n: uint64) { owns p[n - 1u64]; }
int32 probe(int32* p, uint64* count, int32 input) {
    owns *count;
    owns cell(p, old(*count));
    requires 1u64 <= *count;
    requires *count <= 2305843009213693951u64;
    requires valid_place(p[0..*count]);
    requires separate(memory(*count), memory(p[*count - 1u64]));
    ensures result == input;
} by {
    unfold(cell(p, *count));
    execute();
    fold(cell(p, old(*count + 1u64)));
    simp();
}
```

```expect
fail: missing resource
```
