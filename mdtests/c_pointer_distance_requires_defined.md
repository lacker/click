# same-object provenance does not guarantee a representable distance

Two pointers into one C object may still be far enough apart that their
element distance does not fit `int32`. A modular helper must state the
definedness of its subtraction separately from their shared provenance.

```c filename=c_pointer_distance_requires_defined.c
int32 distance(int32 *left, int32 *right) {
    return right - left;
}
```

```click
verifying "c_pointer_distance_requires_defined.c";

int32 distance(int32* left, int32* right) {
    requires same_object(left, right);
    ensures result == result;
} by { execute(); simp(); }
```

```expect
fail: undefined behavior: signed overflow
```
