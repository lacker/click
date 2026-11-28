# A tuple projection past its last component is refused

A pair has components 0 and 1; `p.2` names neither.

```click
theorem past_the_end(p: (int32, int32)) {
    ensures p.2 == p.0;
}
```

```expect
fail: the tuple type `(int32, int32)` has no component 2
```
