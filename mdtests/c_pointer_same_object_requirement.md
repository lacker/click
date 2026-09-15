# same-object requirements preserve pointer provenance through calls

An explicit `same_object` requirement lets a helper compare independently
supplied pointer parameters. The caller discharges it with two pointers into
one array. Relational ordering of members of the same aggregate remains valid.

```c filename=c_pointer_same_object_requirement.c
struct pair {
    int32 first;
    int32 second;
};

int32 compare(int32 *left, int32 *right) {
    return left < right;
}

int32 compare_array_elements(void) {
    int32 values[2] = {1, 2};
    return compare(&values[0], &values[1]);
}

int32 compare_forwarded(int32 *left, int32 *right) {
    return compare(left, right);
}

int32 members_in_order(struct pair *pair) {
    return &pair->first < &pair->second;
}
```

```click
verifying "c_pointer_same_object_requirement.c";

int32 compare(int32* left, int32* right) {
    requires same_object(left, right);
    ensures result == 0 or result == 1;
} by { execute(); simp(); }

int32 compare_array_elements() {
    ensures result == 0 or result == 1;
} by { execute(); simp(); }

int32 compare_forwarded(int32* left, int32* right) {
    requires same_object(left, right);
    ensures result == 0 or result == 1;
} by { execute(); simp(); }

int32 members_in_order(struct pair* pair) {
    requires pair != 0;
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
