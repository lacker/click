# C multidimensional array decay loses the selected row domain

The C frontend flattens a multidimensional scalar array field into one scalar
array domain. This preserves element addresses but permits pointer arithmetic
across a row boundary. A pointer obtained from the first row must retain that
row's extent, even when the following row is initialized and accessible.

Reproduced with the bounded object-model branch's CLI on 2026-10-11: both
contracts below verify. `probe` has undefined behavior; `q + 3` is a valid
one-past pointer for the first row, but dereferencing it is invalid. `control`
is valid and must remain supported.

```c
struct Rows { int values[2][3]; };
int probe(void) {
    struct Rows p = {{{1, 2, 3}, {4, 5, 6}}};
    int *q = &p.values[0][0];
    return q[3];
}
int control(void) {
    struct Rows p = {{{1, 2, 3}, {4, 5, 6}}};
    return p.values[1][0];
}
```

```click
verifying "row.c";
int probe() { ensures result == 4; } by { execute(); simp(); }
int control() { ensures result == 4; } by { execute(); simp(); }
```

The C++ importer does not currently admit nested array types. This defect is
in existing C lowering, not justification for admitting flattened C++ arrays.

Acceptance criteria:

- Preserve the original C above and reject `probe` at its invalid read while
  verifying `control`, including expanded proof checking.
- Retain the selected array-element/row path before inner decay. Check row
  selection, inner stride, and extent against the declared dimensions.
- Allow forming the first row's one-past pointer, reject forming beyond it,
  and reject dereferencing it even if the next row's address compares equal.
- Preserve compact initialization and copying; domain work must not grow with
  the number of unselected elements or rows.
