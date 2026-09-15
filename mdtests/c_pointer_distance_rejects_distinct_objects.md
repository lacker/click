# pointer distance rejects distinct caller objects

A pointer-distance helper may rely on a definedness requirement, but a caller
cannot discharge it with unrelated local objects.

```c filename=c_pointer_distance_rejects_distinct_objects.c
int32 distance(int32 *left, int32 *right) {
    return right - left;
}

int32 distance_locals(void) {
    int32 left = 1;
    int32 right = 2;
    return distance(&left, &right);
}
```

```click
verifying "c_pointer_distance_rejects_distinct_objects.c";

int32 distance(int32* left, int32* right) {
    requires defined(right - left);
    ensures result == (right - left);
} by { execute(); simp(); }

int32 distance_locals() {
    ensures result == result;
} by { execute(); simp(); }
```

```expect
fail: missing prerequisite (distance precondition)
```
