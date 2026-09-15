# null pointers have no object provenance for relational comparison

Null pointers compare equal, but neither points into an array object. A
`same_object` requirement therefore cannot make relational comparison between
two null arguments defined. These helpers cover all four relational pointer
operators before their caller tries to discharge the requirements with nulls.

```c filename=c_pointer_null_order_has_no_object_provenance.c
int32 compare_lt(int32 *left, int32 *right) {
    return left < right;
}

int32 compare_le(int32 *left, int32 *right) {
    return left <= right;
}

int32 compare_gt(int32 *left, int32 *right) {
    return left > right;
}

int32 compare_ge(int32 *left, int32 *right) {
    return left >= right;
}

int32 compare_nulls(void) {
    int32 lt = compare_lt(0, 0);
    int32 le = compare_le(0, 0);
    int32 gt = compare_gt(0, 0);
    int32 ge = compare_ge(0, 0);
    return lt + le + gt + ge;
}
```

```click
verifying "c_pointer_null_order_has_no_object_provenance.c";

int32 compare_lt(int32* left, int32* right) {
    requires same_object(left, right);
    ensures result == 0 or result == 1;
} by { execute(); simp(); }

int32 compare_le(int32* left, int32* right) {
    requires same_object(left, right);
    ensures result == 0 or result == 1;
} by { execute(); simp(); }

int32 compare_gt(int32* left, int32* right) {
    requires same_object(left, right);
    ensures result == 0 or result == 1;
} by { execute(); simp(); }

int32 compare_ge(int32* left, int32* right) {
    requires same_object(left, right);
    ensures result == 0 or result == 1;
} by { execute(); simp(); }

int32 compare_nulls() {
    ensures result >= 0;
} by { execute(); simp(); }
```

```expect
fail: missing prerequisite (compare_lt precondition)
```
