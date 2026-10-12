# Pointer formation respects the selected scalar member

A trivial result contract cannot hide undefined pointer formation inside the
enclosing record's allocation.

```cpp filename=pair.cpp function=probe profile=normal_only
struct Pair { int first; int second; };
int* probe(Pair& pair) noexcept { return &pair.first + 2; }
```

```click
verifying "pair.cpp";
int32* probe(struct Pair& pair) {
    views pair.first;
    views pair.second;
    ensures 1 == 1;
} by { execute(); simp(); }
```

```expect
fail: pointer arithmetic
```
