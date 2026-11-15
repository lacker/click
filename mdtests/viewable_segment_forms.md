# `viewable` segment forms and a stateted viewability fact

This checks the `viewable` spellings of the memory-model page — a constant
range, a symbolic range, and a pointer-base range — and that a proof can name
viewability at a recorded program point with proposition-level `at(...)`.

```c filename=viewable_segment_forms.c
int32 viewable_segment_forms(int32 p[], int32 n) {
    return p[0];
}
```

```click
verifying "viewable_segment_forms.c";

int32 viewable_segment_forms(int32 p[], int32 n) {
    requires n >= 3;
    requires viewable(p[0..3]);
    requires viewable(p[0..n]);
    requires viewable((p + 1)[0..n - 1]);
    views p[0..1];
    ensures returns_first: result == p[0];
} by {
    have at(region(0).entry, viewable(p[0..n])) by {
        known();
    }
}
```

```expect
pass
```
