# Pointer-to-const fields remain assignable and do not freeze aliases

```c filename=main.c
struct holder { const int *value; };
const int *get(struct holder *h) { return h->value; }
void set(struct holder *h, const int *p) { h->value = p; }
int copy_read(const int *p) {
    struct holder h = { p };
    struct holder copy = h;
    return copy.value[0];
}
struct outer { struct holder inner; };
int nested_copy(const int *p) {
    struct outer original = { { p } };
    struct outer copy = original;
    return copy.inner.value[0];
}
const int *sequential_set(struct holder *h, const int *p) {
    WRITE_ONCE(h->value, p);
    return READ_ONCE(h->value);
}
int alias_write(struct holder *h, int *p) {
    *p = 7;
    return h->value[0];
}
```

```click
verifying "main.c";
const int *get(struct holder *h) {
    views &h->value;
    ensures result == h->value;
} by { execute(); simp(); }
void set(struct holder *h, const int *p) {
    owns &h->value;
    ensures h->value == p;
} by { execute(); simp(); }
int copy_read(const int *p) {
    views p[0..1];
    ensures result == p[0];
} by { execute(); simp(); }
int nested_copy(const int *p) {
    views p[0..1];
    ensures result == p[0];
} by { execute(); simp(); }
const int *sequential_set(struct holder *h, const int *p) {
    owns &h->value;
    ensures h->value == p;
    ensures result == p;
} by { execute(); simp(); }
int alias_write(struct holder *h, int *p) {
    views &h->value;
    owns p[0..1];
    requires h->value == p;
    ensures result == 7;
    ensures p[0] == 7;
} by { execute(); simp(); }
```

```expect
pass
```
