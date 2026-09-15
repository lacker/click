# subtracting two null pointers is undefined

`defined(right - left)` includes actual shared object provenance, not merely
equality of the two pointer values. A caller cannot discharge that requirement
by passing two null pointers.

```c filename=c_pointer_null_distance_is_undefined.c
int32 distance(int32 *left, int32 *right) {
    return right - left;
}

int32 distance_nulls(void) {
    return distance(0, 0);
}
```

```click
verifying "c_pointer_null_distance_is_undefined.c";

int32 distance(int32* left, int32* right) {
    requires defined(right - left);
    ensures result == (right - left);
} by { execute(); simp(); }

int32 distance_nulls() {
    ensures result == 0;
} by { execute(); simp(); }
```

```expect
fail: missing prerequisite (distance precondition)
```
