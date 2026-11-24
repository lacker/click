# Folding rejects a wrong cell selected by nested entry arithmetic

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
    views p[0..*count];
    requires separate(memory(*count), memory(p[*count - 1u64]));
    ensures result == input;
} by {
    unfold(cell(p, *count));
    have separate(memory(old(p)[old(*count) - 1u64]), memory(old(p)[0u64..old(*count)])) by { close(); }
    step();
    step_until(function.exit);
    fold(cell(p, old(*count) + 1u64));
    close();
}
```

```expect
fail: missing resource
```
