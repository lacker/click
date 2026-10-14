# Folding an indexed cell keeps the entry count

The C body decrements the descriptor before writing its former last element.
The resource returns ownership of that same cell, using the captured entry
count rather than the descriptor's current count.

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
    fold(cell(p, old(*count)));
    simp();
}
```

```expect
pass
```
