# defined pointer distance is reusable across a call

Pointer subtraction between independently supplied parameters needs both
same-object provenance and a distance representable as `int32`.
`defined(right - left)` states both conditions using the same semantics as the
C body. Same-array callers, including one-past endpoints, discharge it.

```c filename=c_pointer_distance_requirement.c
int32 distance(int32 *left, int32 *right) {
    return right - left;
}

int32 distance_array(void) {
    int32 values[3] = {1, 2, 3};
    return distance(&values[0], &values[2]);
}

int32 distance_one_past(void) {
    int32 values[2] = {1, 2};
    return distance(values, values + 2);
}
```

```click
verifying "c_pointer_distance_requirement.c";

int32 distance(int32* left, int32* right) {
    requires defined(right - left);
    ensures result == (right - left);
} by { execute(); simp(); }

int32 distance_array() {
    ensures result == 2;
} by { execute(); simp(); }

int32 distance_one_past() {
    ensures result == 2;
} by { execute(); simp(); }
```

```expect
pass
```
