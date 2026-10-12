# A one-past member pointer cannot read its sibling

Address coincidence and permission to read the next member do not change the
object selected by a stored pointer.

```cpp filename=pair.cpp function=probe profile=normal_only
struct Pair { int first; int second; };
int probe(Pair& pair) noexcept {
    int* p = &pair.first;
    p = p + 1;
    return *p;
}
```

```click
verifying "pair.cpp";
int32 probe(struct Pair& pair) {
    views pair.first;
    views pair.second;
    ensures result == pair.second;
} by { execute(); simp(); }
```

```expect
fail: invalid memory access
```
